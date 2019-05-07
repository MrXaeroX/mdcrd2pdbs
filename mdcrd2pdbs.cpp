/***************************************************************************
* Copyright (C) 2019 Alexander V. Popov.
* 
* This source code is free software; you can redistribute it and/or 
* modify it under the terms of the GNU General Public License as 
* published by the Free Software Foundation; either version 2 of 
* the License, or (at your option) any later version.
* 
* This source code is distributed in the hope that it will be 
* useful, but WITHOUT ANY WARRANTY; without even the implied 
* warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
* See the GNU General Public License for more details.
* 
* You should have received a copy of the GNU General Public License
* along with this program; if not, write to the Free Software 
* Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
***************************************************************************/
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <cctype>
#include <cmath>
#include <vector>
#include <algorithm>
#include <direct.h>

typedef unsigned __int8 uint8;
typedef unsigned __int16 uint16;
typedef unsigned __int32 uint32;

typedef __int64 fileOfs_t;
#define fu_seek	_fseeki64
#define fu_tell	_ftelli64

typedef union {
	char	string[4];
	uint32	integer;
} name_t;

enum {
	AF_IGNORE = ( 1 << 0 ),
	AF_HEAVY = ( 1 << 1 ),
	AF_SOLVENT = ( 1 << 2 ),
};

typedef struct atom_s {
	uint32	serial;					// Serial number of the atom.
	uint32	resnum;					// Residue number of the atom.
	uint8		chainnum;				// Chain number of the atom.
	uint8		chainid;				// Chain identificator ('A', 'B', etc.).
	uint16	flags;					// Atomic flags (bit combination of AF_xxx).
	uint32	snapcount;			// Number of snapshots where condition was met.
	name_t	title;					// Original name of the atom.
	name_t	residue;				// Original name of the residue.
	name_t	xtitle;					// Fixed atom's title (trimmed and whitespace-expanded).
	name_t	xresidue;				// Fixed residue's title (trimmed and whitespace-expanded).
	float		coords[3];
} atom_t;

namespace
{
int g_argc = 0;
char **g_argv = nullptr;
FILE *current_fp = nullptr;
size_t g_atcount = 0;
atom_t *g_atoms = nullptr;

const char *get_argv( const char *argname, const char *default_value )
{
	for ( int i = 0; i < g_argc; ++i ) {
		if ( !g_argv[i] || g_argv[i][0] != '-' || 
         _stricmp( g_argv[i] + 1, argname ) )
			continue;
		if ( i == g_argc - 1 || g_argv[i+1][0] == '-' )
			return default_value;
		return g_argv[i+1];
	}
	return default_value;
}

int get_int( const char *str, size_t len = 0 )
{
	assert( str != nullptr );
	if ( !str ) 
		return 0;

	const uint8 *src = reinterpret_cast<const uint8*>( str );
	const uint8 *end = &src[len];
	if ( src == end ) while ( *end ) ++end;

#if defined(_DEBUG)
	// sanity check
	char buf[64];
	memset( buf, 0, sizeof(buf) );
	strncpy_s( buf, str, end - src );
	const int check = atoi( buf );
#endif

	// check for empty characters in string
	while ( src != end && (*src) <= 32 ) 
		++src;

	const int sgn = ( *src == '-' ) ? -1 : 1;
	if ( *src == '-' || *src == '+' ) ++src;

	int val = 0;

	// check for hex
	if ( src[0] == '0' && ( src[1] == 'x' || src[1] == 'X' ) ) {
		src += 2;
		while ( src != end ) {
			const int c = *src++;
			if ( c >= '0' && c <= '9' )
				val = ( val << 4 ) + c - '0';
			else if ( c >= 'a' && c <= 'f' )
				val = ( val << 4 ) + c - 'a' + 10;
			else if ( c >= 'A' && c <= 'F' )
				val = ( val << 4 ) + c - 'A' + 10;
			else
				break;
		}
		val *= sgn;
		assert( val == check );
		return val;
	}

	// check for character
	if ( src[0] == '\'' ) {
		val = sgn * src[1];
		assert( val == check );
		return val;
	}

	// assume decimal
	while ( src != end ) {
		const int c = *src++;
		if ( c < '0' || c > '9' ) 
			break;
		val = val * 10 + c - '0';
	}

	val *= sgn;
	assert( val == check );
	return val;
}

float get_float( const char *str, size_t len = 0 )
{
	assert( str != nullptr );
	if ( !str ) 
		return 0;

	const uint8 *src = reinterpret_cast<const uint8*>( str );
	const uint8 *end = &src[len];
	if ( src == end ) while ( *end ) ++end;

#if defined(_DEBUG)
	// sanity check
	char buf[64];
	memset( buf, 0, sizeof(buf) );
	strncpy_s( buf, str, end - src );
	const float check = static_cast<float>( atof( buf ) );
#endif

	// check for empty characters in string
	while ( src != end && (*src) <= 32 ) 
		++src;

	const double sgn = ( *src == '-' ) ? -1.0 : 1.0;
	if ( *src == '-' || *src == '+' ) ++src;

	double val = 0.0;

	// check for hex
	if ( src[0] == '0' && ( src[1] == 'x' || src[1] == 'X' ) ) {
		src += 2;
		while ( src != end ) {
			const int c = *src++;
			if ( c >= '0' && c <= '9' )
				val = ( val * 16 ) + c - '0';
			else if ( c >= 'a' && c <= 'f' )
				val = ( val * 16 ) + c - 'a' + 10;
			else if ( c >= 'A' && c <= 'F' )
				val = ( val * 16 ) + c - 'A' + 10;
			else
				break;
		}
		val *= sgn;
		assert( fabs( val - check ) < 0.00001 );
		return static_cast<float>( val );
	}

	// check for character
	if ( src[0] == '\'' ) {
		val = sgn * src[1];
		assert( fabs( val - check ) < 0.00001 );
		return static_cast<float>( val );
	}

	// assume decimal
	int decimal = -1;
	int total = 0;
	int exponent = 0;
	int expsgn = 0;

	while ( src != end ) {
		int c = *src++;
		if ( c == '.' ) {
			decimal = total;
			continue;
		} else if ( c == 'e' || c == 'E' ) {
			c = *src++;
			if ( c == '-' ) {
				expsgn = -1;
				continue;
			} else {
				expsgn = 1;
				if ( c == '+' )
					continue;
			}
		} 
		if ( c < '0' || c > '9' )
			break;
		if ( expsgn )
			exponent = exponent * 10 + c - '0';
		else {
			val = val * 10 + c - '0';
			++total;
		}
	}

	if ( expsgn > 0 ) {
		while ( exponent-- )
			val *= 10;
	} else if ( expsgn < 0 ) {
		while ( exponent-- )
			val /= 10;
	}

	if ( decimal == -1 ) {
		val *= sgn;
		assert( val == check );
		return static_cast<float>( val );
	}

	while ( total --> decimal )
		val /= 10;

	val *= sgn;

	assert( fabs( val - check ) < 0.00001 );
	return static_cast<float>( val );
}

void copy_trimmed( name_t *dst, const name_t *src )
{
	size_t dstpos = 0;
	const uint8 *srcbytes = reinterpret_cast<const uint8*>( src->string );
	uint8 *dstbytes = reinterpret_cast<uint8*>( dst->string );
	for ( size_t i = 0; i < 4; ++i, ++srcbytes ) {
		if ( *srcbytes > 32 ) dstbytes[dstpos++] = toupper( *srcbytes );
	}
	for ( size_t i = dstpos; i < 4; ++i )
		dstbytes[i] = ' ';
}

bool write_pdb_file( const char *filename, const char *condition, 
                     uint32 min_snapcount, uint32 total_snapcount )
{
	FILE *fp = fopen( filename, "wb" );
	if ( !fp )
		return false;

	uint32 write_atom_counter = 0;
	uint32 write_residue_counter = 0;
	uint32 solvent_chain_id = 1;
	bool switch_to_solvent = false;

	const atom_t *at = g_atoms;
	uint32 prev_resnum = -1;
	uint32 prev_snapcount = 0;
	std::vector<size_t> residue_indices;
	std::vector<std::pair<size_t,std::pair<uint32,uint32>>> residue_snapcount;
	residue_indices.reserve( 512 );
	residue_snapcount.reserve( 512 );
	for ( size_t i = 0; i < g_atcount; ++i, ++at ) {
		if ( at->flags & AF_IGNORE )
			continue;
		if ( !( at->flags & AF_SOLVENT ) ) {
			write_residue_counter = at->resnum + 1;
			continue;
		}
		if ( at->resnum != prev_resnum ) {
			if ( !residue_indices.empty() ) {
				for ( auto it = residue_indices.cbegin(); it != residue_indices.cend();
              ++it )
					g_atoms[*it].snapcount = prev_snapcount;
				residue_indices.clear();
				if ( min_snapcount && prev_snapcount >= min_snapcount ) {
					residue_snapcount.push_back( std::make_pair( i, 
							std::make_pair( write_residue_counter, prev_snapcount ) ) );
					++write_residue_counter;
				}
			}
			prev_snapcount = 0;
			prev_resnum = at->resnum;
		}
		residue_indices.push_back( i );
		if ( at->flags & AF_HEAVY ) {
			if ( at->snapcount > prev_snapcount )
				prev_snapcount = at->snapcount;
		}
	}

	if ( !residue_snapcount.empty() ) {
		fprintf( fp, "%-6s -----------------------------------------------\n",
             "REMARK" );
		fprintf( fp, "%-6s Solvent residues%s:\n", "REMARK",
             condition ? condition : "" );
		fprintf( fp, "%-6s -----------------------------------------------\n",
             "REMARK" );
		for ( auto it = residue_snapcount.cbegin(); it != residue_snapcount.cend();
          ++it ) {
			fprintf( fp, "%-6s  %.3s-%u: occurence %u/%u (%u%%)\n", "REMARK", 
					g_atoms[it->first].xresidue.string, it->second.first, 
					it->second.second, total_snapcount,
					it->second.second * 100 / total_snapcount );
		}
		fprintf( fp, "%-6s -----------------------------------------------\n",
             "REMARK" );
	}

	at = g_atoms;
	prev_resnum = 1;
	write_residue_counter = 0;
	for ( size_t i = 0; i < g_atcount; ++i, ++at ) {
		if ( at->flags & AF_IGNORE )
			continue;
		if ( ( at->flags & AF_SOLVENT ) && min_snapcount &&
         at->snapcount < min_snapcount )
			continue;
		uint8 chain_id;
		if ( at->flags & AF_SOLVENT ) {
			if ( !switch_to_solvent ) {
				prev_resnum = 0;
				switch_to_solvent = true;
				fprintf( fp, "%-6s%5u\n", "TER", write_atom_counter );
			}
			chain_id = 'A' + solvent_chain_id;
			if ( at->resnum != prev_resnum ) {
				prev_resnum = at->resnum;
				++write_residue_counter;
				if ( write_residue_counter > 9999 ) {
					fprintf( fp, "%-6s%5u\n", "TER", write_atom_counter );
					++solvent_chain_id;
					++chain_id;
					write_residue_counter = 1;
				}
			}
		} else {
			chain_id = at->chainid;
			write_residue_counter = at->resnum;
			switch_to_solvent = false;
		}
		++write_atom_counter;
		fprintf( fp, "%-6s%5u %.4s %.3s %c%4u    %8.3f%8.3f%8.3f\n", "ATOM", 
				write_atom_counter, at->xtitle.string, at->xresidue.string, chain_id, 
				write_residue_counter,	at->coords[0], at->coords[1], at->coords[2] );
	}
	fprintf( fp, "%-6s\n", "END" );
	fclose( fp );
	return true;
}

void print_horz_line()
{
	printf( "%s\n", "----------------------------------------------------" );
}

void final_cleanup()
{
	if ( current_fp )
		fclose( current_fp );
}
}

int main( int argc, char *argv[] )
{
	g_argc = argc - 1;
	g_argv = argv + 1;
	atexit( &final_cleanup );

	// Get and validate parameters.
	int final_snapshot = get_int( get_argv( "final", "100" ) );
	const int start_snapshot = get_int( get_argv( "start", "0" ) );
	const char *topo_file = get_argv( "topo", nullptr );
	const char *traj_file = get_argv( "traj", nullptr );
	const char *out_pdb_name = get_argv( "out", "molMdRes" );
	const float cond_dist = get_float( get_argv( "cond_within", "5.0" ) );
	const char *cond_res = get_argv( "cond_res", nullptr );
	const float cond_cutoff = get_float( get_argv( "cond_cutoff", "10" ) );

	printf( "%s\n", "mdcrd2pdbs version 1.0 by Alexander V. Popov" );
	print_horz_line();
	printf( "%-21s%s\n", "Topology file:", topo_file );
	printf( "%-21s%s\n", "Input trajectory:", traj_file );
	printf( "%-21s%i\n", "  Start snapshot:", start_snapshot );
	printf( "%-21s%i\n", "  Final snapshot:", final_snapshot );
	printf( "%-21s%.2f A\n", "(Condition) within:", cond_dist );
	printf( "%-21s%s\n", "(Condition) resname:", cond_res );
	printf( "%-21s%g%%\n", "(Condition) cutoff:", cond_cutoff );
	printf( "%-21s%s\n", "Output PDB mask:", out_pdb_name );
	print_horz_line();
	
	if ( !topo_file || !traj_file ) {
		printf( "ERROR: missing input file names.\n" );
		return 1;
	}
	if ( final_snapshot <= start_snapshot ) {
		printf( "ERROR: bad snapshot indices.\n" );
		return 1;
	}

	// Build human-readable condition string.
	char hr_condition_string[256] = { 0 };
	if ( cond_res )
		sprintf( hr_condition_string, " within %.2fA of %s", cond_dist, cond_res );

	// Read topology data.
	current_fp = fopen( topo_file, "rb" );
	if ( !current_fp ) {
		printf( "ERROR: can't read topology from \"%s\".\n", topo_file );
		return 1;
	}
	g_atcount = 0;
	size_t rescount = 0;
	{
		char line[96];
		while ( fgets( line, sizeof(line), current_fp ) ) {
			if ( *line != '%' ) continue;
			if ( !strncmp( line, "%FLAG POINTERS", 14 ) ) {
				fgets( line, sizeof(line), current_fp );
				if ( strncmp( line, "%FORMAT(10I8)", 13 ) ) {
					printf( "ERRPR: invalid FORMAT in section POINTERS in \"%s\"!\n",
                  topo_file );
					return 1;
				}
				fgets( line, sizeof(line), current_fp );
				g_atcount = get_int( line, 8 );
				fgets( line, sizeof(line), current_fp );
				rescount = get_int( line + 8, 8 );
				break;
			}
		}
		if ( !g_atcount ) {
			printf( "ERROR: \"%s\" doesn't contain any atoms!\n", topo_file );
			return 1;
		}
		if ( !rescount ) {
			printf( "ERROR: \"%s\" doesn't contain any residues!\n", topo_file );
			return 1;
		}
		g_atoms = static_cast<atom_t*>( calloc( g_atcount, sizeof(atom_t) ) );
		name_t *resnames = static_cast<name_t*>(
        calloc( rescount, sizeof(name_t) ) );
		while ( fgets( line, sizeof(line), current_fp ) ) {
			if ( *line != '%' ) continue;
			if ( !strncmp( line, "%FLAG ATOM_NAME", 15 ) ) {
				// Parse atom titles.
				fgets( line, sizeof(line), current_fp );
				if ( strncmp( line, "%FORMAT(20a4)", 13 ) ) {
					printf( "ERROR: invalid FORMAT in section ATOM_NAME in \"%s\"!\n",
                  topo_file );
					return 1;
				}
				atom_t *at = g_atoms;
				for ( size_t i = 0; i < g_atcount; ++i, ++at ) {
					const size_t col = i % 20;
					if ( !col ) fgets( line, sizeof(line), current_fp );
					at->serial = static_cast<uint32>( i + 1 );
					memcpy( at->title.string, line + 4*col, 4 );
					copy_trimmed( &at->xtitle, &at->title );
				}
			} else if ( !strncmp( line, "%FLAG RESIDUE_LABEL", 19 ) ) {
				// Parse residue names.
				fgets( line, sizeof(line), current_fp );
				if ( strncmp( line, "%FORMAT(20a4)", 13 ) ) {
					printf( "ERROR: invalid FORMAT in section RESIDUE_LABEL in \"%s\"!\n",
                  topo_file );
					return 1;
				}
				name_t *res = resnames;
				for ( size_t i = 0; i < rescount; ++i, ++res ) {
					const size_t col = i % 20;
					if ( !col ) fgets( line, sizeof(line), current_fp );
					for ( size_t i = 0; i < 4; ++i )
						res->string[i] = toupper( line[4*col+i] );
					if ( res->string[3] == ' ' ) res->string[3] = '\0';
				}
			} else if ( !strncmp( line, "%FLAG RESIDUE_POINTER", 21 ) ) {
				// Assign residue names to atoms.
				fgets( line, sizeof(line), current_fp );
				if ( strncmp( line, "%FORMAT(10I8)", 13 ) ) {
					printf(
              "ERROR: invalid FORMAT in section RESIDUE_POINTER in \"%s\"!\n",
              topo_file );
					return 1;
				}
				name_t *prevres, *res = resnames;
				size_t prev = 0, current;
				int resid = 1;
				for ( size_t i = 0; i < rescount; ++i, ++res ) {
					const size_t col = i % 10;
					if ( !col ) fgets( line, sizeof(line), current_fp );
					current = get_int( line + 8*col, 8 );
					assert( current > prev );
					if ( prev ) {
						for ( size_t i = prev; i < current; ++i ) {
							g_atoms[i-1].chainid = 'A';
							g_atoms[i-1].chainnum = 1;
							g_atoms[i-1].resnum = resid;
							g_atoms[i-1].residue.integer = prevres->integer;
							g_atoms[i-1].xresidue.integer = prevres->integer;
							if ( prevres->string[3] == '\0' )
                g_atoms[i-1].xresidue.string[3] = ' ';
						}
						++resid;
					}
					prev = current;
					prevres = res;
				}
				if ( prev ) {
					for ( size_t i = prev; i <= g_atcount; ++i ) {
						g_atoms[i-1].chainid = 'A';
						g_atoms[i-1].chainnum = 1;
						g_atoms[i-1].resnum = resid;
						g_atoms[i-1].residue.integer = prevres->integer;
						g_atoms[i-1].xresidue.integer = prevres->integer;
						if ( prevres->string[3] == '\0' )
              g_atoms[i-1].xresidue.string[3] = ' ';
					}
				}
			}
		}
		free( resnames );
	}
	fclose( current_fp );
	current_fp = nullptr;

	// Set atom flags.
	size_t first_solvent_atom = ~0;
	{
		name_t solvent_name;
		solvent_name.string[0] = 'W';
		solvent_name.string[1] = 'A';
		solvent_name.string[2] = 'T';
		solvent_name.string[3] = ' ';
		name_t ions_name;
		ions_name.string[0] = 'N';
		ions_name.string[1] = 'A';
		ions_name.string[2] = '+';
		ions_name.string[3] = ' ';
		atom_t *at = g_atoms;
		int num_solvent_atoms = 0, num_ions = 0;
		for ( size_t i = 0; i < g_atcount; ++i, ++at ) {
			for ( size_t j = 0; j < 4; ++j ) {
				if ( at->xtitle.string[j] != ' ' ) {
					if ( at->xtitle.string[j] != 'H' )
						at->flags |= AF_HEAVY;
					break;
				}
			}
			if ( at->xresidue.integer == solvent_name.integer ) {
				at->flags |= AF_SOLVENT;
				++num_solvent_atoms;
				if ( i < first_solvent_atom )
					first_solvent_atom = i;
			} else if ( at->xresidue.integer == ions_name.integer ) {
				at->flags |= AF_IGNORE;
				++num_ions;
			}
		}
		printf( "Found %i solvent atoms, %i ions.\n", num_solvent_atoms, num_ions );
	}
	// Open the trajectory.
	current_fp = fopen( traj_file, "rb" );
	if ( !current_fp ) {
		printf( "ERROR: can't read trajectory from \"%s\".\n", traj_file );
		return 1;
	}
	{
		char line[96];
		fgets( line, sizeof(line), current_fp );  // Skip header.
		// Estimate coordinate frame size.
		int frame_size_in_lines = static_cast<int>( ( g_atcount * 3 + 9 ) / 10 );
		fileOfs_t frame_start = fu_tell( current_fp );
		for ( int i = 0; i < frame_size_in_lines; ++i ) {
			if ( !fgets( line, sizeof(line), current_fp ) ) {
				printf( "ERROR: incomplete frame in \"%s\"!\n", traj_file );
				return 1;
			}
		}
		fileOfs_t frame_end = fu_tell( current_fp );
		// Now read the next line and check if it has exactly 3 items.
		// If that's the case, assume we have PBC enabled.
		if ( fgets( line, sizeof(line), current_fp ) ) {
			float temp[4];
			if ( sscanf_s( line, "%f %f %f %f", 
                     &temp[0], &temp[1], &temp[2], &temp[3] ) == 3 ) {
				++frame_size_in_lines;
				frame_end = fu_tell( current_fp );
				printf( "PBC were detected in the trajectory.\n" );
			}
		}
		// Now we have the whole frame read, estimate its size in bytes.
		const size_t framesize = static_cast<size_t>( frame_end - frame_start );
		const fileOfs_t framebase = frame_start + framesize * start_snapshot;
		char *framebuf = static_cast<char*>( calloc( 1, framesize ) );
		// Count total frames.
		fu_seek( current_fp, 0, SEEK_END );
		const fileOfs_t file_end = fu_tell( current_fp );
		const fileOfs_t total_frames = ( file_end - frame_start ) / framesize;
		printf( "Estimated trajectory size: %i snapshot(s).\n", total_frames );
		if ( final_snapshot >= total_frames ) {
			final_snapshot = static_cast<int>( total_frames - 1 );
			printf(
          "WARNING: final snapshot out of trajectory bounds, reset to %i.\n",
          final_snapshot );
		}
		// Reading pass: evaluate condition for all solvent atoms.
		const bool has_condition = cond_res && *cond_res && cond_dist >= 0.0f;
		uint32 min_snapcount = 0;
		if ( has_condition ) {
			rewind( current_fp );
			// Get list of condition atoms.
			name_t cond_name;
			size_t cond_size = 0;
			for ( const char *s = cond_res; *s; ++s, ++cond_size )
				cond_name.string[cond_size] = toupper( *s );
			for ( ; cond_size < 4; ++cond_size )
				cond_name.string[cond_size] = ' ';
			std::vector<uint32> condition_atoms;
			condition_atoms.reserve( 200 );
			atom_t *at = g_atoms;
			for ( size_t i = 0; i < g_atcount; ++i, ++at ) {
				if ( at->flags & ( AF_SOLVENT | AF_IGNORE ) )
					continue;
				if ( at->xresidue.integer == cond_name.integer )
					condition_atoms.push_back( i );
			}
			printf( "%u atoms of conditional residue %s found.\n",
							condition_atoms.size(), cond_res );
			const float cond_dist_sq = cond_dist * cond_dist;
			printf( "Evaluating condition for solvent molecules: " );
			uint32 processed_frames = 0;
			fu_seek( current_fp, framebase, SEEK_SET );
			const int total_count = final_snapshot - start_snapshot + 1;
			for ( int c = start_snapshot; c <= final_snapshot; ++c,
            ++processed_frames ) {
				const size_t readsize = fread( framebuf, 1, framesize, current_fp );
				if ( readsize != framesize ) {
					printf( "\nERROR: couldn't read snapshot #%i\n", c );
					break;
				}
				printf( "\rEvaluating condition for solvent molecules: %u/%u",
                processed_frames + 1, total_count );
				bool eof = false;
				atom_t *at = g_atoms;
				size_t framepos = 0;
				for ( size_t i = 0; i < g_atcount && !eof; ++i, ++at ) {
					for ( size_t j = 0; j < 3; ++j ) {
						const size_t col = ( i * 3 + j ) % 10;
						if ( !col ) {
							const int linebase = framepos;
							while ( framebuf[framepos] && framebuf[framepos] != '\n' )
                ++framepos;
							if ( framepos >= readsize - 1 ) {
								eof = true;
								break;
							}
							const size_t linesize = std::min( framepos - linebase, 
                                                sizeof(line)-1 );
							assert( linesize > 0 );
							if ( linesize == 0 ) {
								eof = true;
								break;
							}
							memcpy( line, framebuf + linebase, linesize );
							line[linesize] = '\0';
							++framepos;
						}
						at->coords[j] = get_float( line + 8 * col, 8 );
					}
				}
				if ( eof ) {
					printf( "\nERROR: EOF while reading snapshot #%i\n", c );
					break;
				}
				// Now, for each solvent residue, test condition.
				at = g_atoms + first_solvent_atom;
				uint32 prev_resnum = ~0;
				bool prev_eval_ok = false;
				for ( size_t i = first_solvent_atom; i < g_atcount; ++i, ++at ) {
					if ( !( at->flags & AF_SOLVENT ) || !( at->flags & AF_HEAVY ) )
						continue;
					if ( at->resnum == prev_resnum ) {
						if ( prev_eval_ok )
							++at->snapcount;
					} else {
						prev_resnum = at->resnum;
						prev_eval_ok = false;
						for ( auto it = condition_atoms.cbegin();
                  it != condition_atoms.cend(); ++it ) {
							const float dx = at->coords[0] - g_atoms[*it].coords[0];
							const float dy = at->coords[1] - g_atoms[*it].coords[1];
							const float dz = at->coords[2] - g_atoms[*it].coords[2];
							const float dist_sq = dx * dx + dy * dy + dz * dz;
							if ( dist_sq < cond_dist_sq ) {
								++at->snapcount;
								prev_eval_ok = true;
								break;
							}
						}
					}
				}
			}
			// By default, must exist in 10% if trajectory.
			min_snapcount = static_cast<uint32>(
          ceilf( 0.01f * processed_frames * cond_cutoff  ) );
			printf( "\n" );
		}
		// Reading pass: read coordinates and write PDB files.
		rewind( current_fp );
		printf( "Writing output PDB files: " );
		{
			char pdbfilename[260];
			fu_seek( current_fp, framebase, SEEK_SET );
			uint32 pdb_index = 0;
			const int total_count = final_snapshot - start_snapshot + 1;
			for ( int c = start_snapshot; c <= final_snapshot; ++c ) {
				const size_t readsize = fread( framebuf, 1, framesize, current_fp );
				if ( readsize != framesize ) {
					printf( "\nERROR: couldn't read snapshot #%i\n", c );
					break;
				}
				bool eof = false;
				atom_t *at = g_atoms;
				size_t framepos = 0;
				for ( size_t i = 0; i < g_atcount && !eof; ++i, ++at ) {
					for ( size_t j = 0; j < 3; ++j ) {
						const size_t col = ( i * 3 + j ) % 10;
						if ( !col ) {
							const int linebase = framepos;
							while ( framebuf[framepos] && framebuf[framepos] != '\n' )
                ++framepos;
							if ( framepos >= readsize - 1 ) {
								eof = true;
								break;
							}
							const size_t linesize = std::min( framepos - linebase,
                                                sizeof(line)-1 );
							assert( linesize > 0 );
							if ( linesize == 0 ) {
								eof = true;
								break;
							}
							memcpy( line, framebuf + linebase, linesize );
							line[linesize] = '\0';
							++framepos;
						}
						at->coords[j] = get_float( line + 8 * col, 8 );
					}
				}
				if ( eof ) {
					printf( "\nERROR: EOF while reading snapshot #%i\n", c );
					break;
				}
				++pdb_index;
				memset( pdbfilename, 0, sizeof(pdbfilename) );
				sprintf( pdbfilename, "%s%04u.pdb", out_pdb_name, pdb_index );
				printf( "\rWriting output PDB files: %u/%u", pdb_index, total_count );
				if ( !write_pdb_file( pdbfilename, hr_condition_string, min_snapcount,
                              total_count ) ) {
					printf( "\nERROR: couldn't save snapshot #%i to \"%s\"\n", c,
                  pdbfilename );
					break;
				}
			}
		}
		printf( "\n" );
		free( framebuf );
	}
	fclose( current_fp );
	current_fp = nullptr;
	printf( "All done.\n\n" );

	return 0;
}
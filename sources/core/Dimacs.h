/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>
#include <vector>
#include <unordered_set>

#include "utils/ParseUtils.h"
#include "core/SolverTypes.h"
#include "mtl/Sort.h"

namespace Minisat {

//=================================================================================================
// DIMACS Parser:
inline uint32_t murmur_32_scramble(uint32_t k) {
        k *= 0xcc9e2d51;
        k = (k << 15) | (k >> 17);
        k *= 0x1b873593;
        return k;
    }

// 使得输出的哈希值具有良好的分布性和随机性，适用于各种哈希表和哈希集合的应用场景
uint32_t murmur3_vec(uint32_t *data, uint32_t size, uint32_t seed) {
    uint32_t h = seed;
    for (uint32_t i = 0; i < size; i++) {
        h ^= murmur_32_scramble(data[i]);
        h = (h << 13) | (h >> 19);
        h = h * 5 + 0xe6546b64;
    }
    h ^= size;
    h ^= h >> 16;
    h *= 0x85ebca6b;
    h ^= h >> 13;
    h *= 0xc2b2ae35;
    h ^= h >> 16;
    return h;
}

template<class B, class Solver>
static void readClause(B& in, Solver& S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var >= S.nVars()) S.newVar();
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

struct VectorHash {
    size_t operator()(const std::vector<int> &lits) const {
        std::size_t seed = 0;
        seed = murmur3_vec((uint32_t *) lits.data(), lits.size(), 0);
        return seed;
    }
};


template<class B, class Solver>
static void parse_DIMACS_main(B& in, Solver& S) {
    vec<Lit> lits;
    int vars    = 0;
    int clauses = 0;
    int cnt     = 0;

    std::vector<int> record;
    std::unordered_set<std::vector<int>, VectorHash> cache;

    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p'){
            if (eagerMatch(in, "p cnf")){
                vars    = parseInt(in);
                clauses = parseInt(in);
                // SATRACE'06 hack
                // if (clauses > 4000000)
                //     S.eliminate(true);
            }else{
                printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else {
            cnt++;
            readClause(in, S, lits);
            sort(lits);

            record.resize(lits.size());
            for (int i = 0; i < lits.size(); ++i) record[i] = toInt(lits[i]);

            if (cache.find(record) == cache.end()) {
                S.addClause_(lits, false);
                cache.insert(record);
            }
        }
    }
    if (vars != S.nVars())
      // fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of variables.\n");
      printf("WARNING! DIMACS header mismatch: wrong number of variables.\n");
    if (cnt  != clauses)
      //  fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
      printf("WARNING! DIMACS header mismatch: wrong number of clauses.\n");
}

// Inserts problem into solver.
//
template<class Solver>
static void parse_DIMACS(gzFile input_stream, Solver& S) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, S); }

//=================================================================================================

template<class B, class Solver>
static void simple_readClause(B& in, Solver& S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

template<class B, class Solver>
static void check_solution_DIMACS_main(B& in, Solver& S) {
    vec<Lit> lits;
    //    int vars    = 0;
    int clauses=0;
    int cnt     = 0;
    bool ok=true;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p'){
            if (eagerMatch(in, "p cnf")){
              //  vars    = parseInt(in);
                clauses = parseInt(in);
		clauses = parseInt(in);
                // SATRACE'06 hack
                // if (clauses > 4000000)
                //     S.eliminate(true);
            }else{
                printf("c PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else{
            cnt++;
            int parsed_lit, var;
            bool ok=false;
	    lits.clear();
            for(;;) {
                parsed_lit = parseInt(in);
                if (parsed_lit == 0) break; //{printf("\n"); break;}
                var = abs(parsed_lit)-1;
		lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
                // printf("%d ", parsed_lit);
                if ((parsed_lit>0 && S.model[var]==l_True) ||
                        (parsed_lit<0 && S.model[var]==l_False))
                    ok=true;
            }
            if (!ok) {
                printf("c clause %d is not satisfied\n", cnt);
		for(int i=0; i<lits.size(); i++)
		  printf("%d ", toInt(lits[i]));
		printf("\n");
                ok=false;
                // break;
            }
	    assert(ok);
        }
    }
    if (cnt  != clauses)
        printf("c WARNING! DIMACS header mismatch: wrong number of clauses.%d %d\n", cnt, clauses);
    if (ok)
      printf("c solution checked against the original DIMACS file\n");
}

template<class Solver>
static void check_solution_DIMACS(gzFile input_stream, Solver& S) {
    StreamBuffer in(input_stream);
    check_solution_DIMACS_main(in, S); }

//=================================================================================================
}

#endif


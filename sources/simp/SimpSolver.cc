/***********************************************************************************[SimpSolver.cc]
MiniSat -- Copyright (c) 2006,      Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh
 
Maple_LCM, Based on MapleCOMSPS_DRUP -- Copyright (c) 2017, Mao Luo, Chu-Min LI, Fan Xiao: implementing a learnt clause minimisation approach
Reference: M. Luo, C.-M. Li, F. Xiao, F. Manya, and Z. L. , “An effective learnt clause minimization approach for cdcl sat solvers,” in IJCAI-2017, 2017, pp. to–appear.
 
Maple_LCM_Dist, Based on Maple_LCM -- Copyright (c) 2017, Fan Xiao, Chu-Min LI, Mao Luo: using a new branching heuristic called Distance at the beginning of search
 
 
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

#include "mtl/Sort.h"
#include "simp/SimpSolver.h"
#include "utils/System.h"

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "SIMP";

static BoolOption   opt_use_asymm        (_cat, "asymm",        "Shrink clauses by asymmetric branching.", false);
static BoolOption   opt_use_rcheck       (_cat, "rcheck",       "Check if a clause is already implied. (costly)", false);
static BoolOption   opt_use_elim         (_cat, "elim",         "Perform variable elimination.", true);
static IntOption    opt_grow             (_cat, "grow",         "Allow a variable elimination step to grow by a number of clauses.", 0);
static IntOption    opt_clause_lim       (_cat, "cl-lim",       "Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit", 20,   IntRange(-1, INT32_MAX));
static IntOption    opt_subsumption_lim  (_cat, "sub-lim",      "Do not check if subsumption against a clause larger than this. -1 means no limit.", 1000, IntRange(-1, INT32_MAX));
static DoubleOption opt_simp_garbage_frac(_cat, "simp-gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered during simplification.",  0.5, DoubleRange(0, false, HUGE_VAL, false));


//=================================================================================================
// Constructor/Destructor:


SimpSolver::SimpSolver() :
    parsing            (false)
  , grow               (opt_grow)
  , clause_lim         (opt_clause_lim)
  , subsumption_lim    (opt_subsumption_lim)
  , simp_garbage_frac  (opt_simp_garbage_frac)
  , use_asymm          (opt_use_asymm)
  , use_rcheck         (opt_use_rcheck)
  , use_elim           (opt_use_elim)
  , merges             (0)
  , asymm_lits         (0)
  , eliminated_vars    (0)
  , elimorder          (1)
  , use_simplification (true)
  , occurs             (ClauseDeleted(ca))
  , elim_heap          (ElimLt(n_occ))
  , bwdsub_assigns     (0)
  , n_touched          (0)
{
    vec<Lit> dummy(1,lit_Undef);
    //    ca.extra_clause_field = true; // NOTE: must happen before allocating the dummy clause below.
    bwdsub_tmpunit        = ca.alloc(dummy);
    remove_satisfied      = false;
}


SimpSolver::~SimpSolver()
{
}


Var SimpSolver::newVar(bool sign, bool dvar) {
    Var v = Solver::newVar(sign, dvar);

    frozen       .push((char)false);
    // eliminated.push((char)false);

    savedAssigns .push(l_Undef);

    if (use_simplification){
        // n_occ     .push(0);
        // n_occ     .push(0);
        occurs    .init(v);
        touched   .push(0);
        elim_heap .insert(v);
    }
    return v; }



lbool SimpSolver::solve_(bool do_simp, bool turn_off_simp)
{
    vec<Var> extra_frozen;
    lbool    result = l_True;

    for(int v=0; v<nVars(); v++)
      repr[v] = v;
    
    do_simp &= use_simplification;

    if (do_simp){
        // Assumptions must be temporarily frozen to run variable elimination:
        for (int i = 0; i < assumptions.size(); i++){
            Var v = var(assumptions[i]);

            // If an assumption has been eliminated, remember it.
            assert(!isEliminated(v));

            if (!frozen[v]){
                // Freeze and store.
                setFrozen(v, true);
                extra_frozen.push(v);
            } }

        result = lbool(eliminate(turn_off_simp));
    }
    compactCNF();
    if (result == l_True)
        result = Solver::solve_();
    else if (verbosity >= 1)
        printf("c ===============================================================================\n");

    if (result == l_True) {
      restoreElimValue();
        extendModel();
    }

    if (do_simp)
        // Unfreeze the assumptions that were frozen:
        for (int i = 0; i < extra_frozen.size(); i++)
            setFrozen(extra_frozen[i], false);

    return result;
}



bool SimpSolver::addClause_(vec<Lit>& ps, bool sadd)
{
#ifndef NDEBUG
    for (int i = 0; i < ps.size(); i++)
        assert(!isEliminated(var(ps[i])));
#endif

    int nclauses = clauses.size();

    if (use_rcheck && implied(ps))
        return true;

    if (!Solver::addClause_(ps, sadd))
        return false;

    if (!parsing && drup_file) {
      writeClause2drup('a', ps, drup_file);
// #ifdef BIN_DRUP
//         binDRUP('a', ps, drup_file);
// #else
//         for (int i = 0; i < ps.size(); i++)
//             fprintf(drup_file, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
//         fprintf(drup_file, "0\n");
// #endif
    }

    if (use_simplification && clauses.size() == nclauses + 1){
        CRef          cr = clauses.last();
        const Clause& c  = ca[cr];

        // NOTE: the clause is added to the queue immediately and then
        // again during 'gatherTouchedClauses()'. If nothing happens
        // in between, it will only be checked once. Otherwise, it may
        // be checked twice unnecessarily. This is an unfortunate
        // consequence of how backward subsumption is used to mimic
        // forward subsumption.
        subsumption_queue.insert(cr);
        for (int i = 0; i < c.size(); i++){
            occurs[var(c[i])].push(cr);
            n_occ[toInt(c[i])]++;
            touched[var(c[i])] = 1;
            n_touched++;
            if (elim_heap.inHeap(var(c[i])))
                elim_heap.increase(var(c[i]));
        }
    }

    return true;
}


void SimpSolver::removeClause(CRef cr)
{
    const Clause& c = ca[cr];

    if (use_simplification)
        for (int i = 0; i < c.size(); i++){
            n_occ[toInt(c[i])]--;
            updateElimHeap(var(c[i]));
            occurs.smudge(var(c[i]));
        }

    Solver::removeClause(cr);
}


bool SimpSolver::strengthenClause(CRef cr, Lit l)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);
    assert(use_simplification);

    // FIX: this is too inefficient but would be nice to have (properly implemented)
    // if (!find(subsumption_queue, &c))
    subsumption_queue.insert(cr);

    if (drup_file){
      strengthenClause2drup(c, l, drup_file);
// #ifdef BIN_DRUP
//         binDRUP_strengthen(c, l, drup_file);
// #else
//         for (int i = 0; i < c.size(); i++)
//             if (c[i] != l) fprintf(drup_file, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
//         fprintf(drup_file, "0\n");
// #endif
    }

    if (c.size() == 2){
        removeClause(cr);
        c.strengthen(l);
    }else{
        if (drup_file){
	  writeClause2drup('d', c, drup_file);
// #ifdef BIN_DRUP
//             binDRUP('d', c, drup_file);
// #else
//             fprintf(drup_file, "d ");
//             for (int i = 0; i < c.size(); i++)
//                 fprintf(drup_file, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
//             fprintf(drup_file, "0\n");
// #endif
        }

        detachClause(cr, true);
        c.strengthen(l);
        attachClause(cr);
        remove(occurs[var(l)], cr);
        n_occ[toInt(l)]--;
        updateElimHeap(var(l));
    }

    return c.size() == 1 ? enqueue(c[0]) && propagate() == CRef_Undef : true;
}


// // Returns FALSE if clause is always satisfied ('out_clause' should not be used).
// bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
// {
//     merges++;
//     out_clause.clear();

//     bool  ps_smallest = _ps.size() < _qs.size();
//     const Clause& ps  =  ps_smallest ? _qs : _ps;
//     const Clause& qs  =  ps_smallest ? _ps : _qs;

//     for (int i = 0; i < qs.size(); i++){
//         if (var(qs[i]) != v){
//             for (int j = 0; j < ps.size(); j++)
//                 if (var(ps[j]) == var(qs[i]))
//                     if (ps[j] == ~qs[i])
//                         return false;
//                     else
//                         goto next;
//             out_clause.push(qs[i]);
//         }
//         next:;
//     }

//     for (int i = 0; i < ps.size(); i++)
//         if (var(ps[i]) != v)
//             out_clause.push(ps[i]);

//     return true;
// }


// // Returns FALSE if clause is always satisfied.
// bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, int& size)
// {
//     merges++;

//     bool  ps_smallest = _ps.size() < _qs.size();
//     const Clause& ps  =  ps_smallest ? _qs : _ps;
//     const Clause& qs  =  ps_smallest ? _ps : _qs;
//     const Lit*  __ps  = (const Lit*)ps;
//     const Lit*  __qs  = (const Lit*)qs;

//     size = ps.size()-1;

//     for (int i = 0; i < qs.size(); i++){
//         if (var(__qs[i]) != v){
//             for (int j = 0; j < ps.size(); j++)
//                 if (var(__ps[j]) == var(__qs[i]))
//                     if (__ps[j] == ~__qs[i])
//                         return false;
//                     else
//                         goto next;
//             size++;
//         }
//         next:;
//     }

//     return true;
// }


void SimpSolver::gatherTouchedClauses()
{
    if (n_touched == 0) return;

    int i,j;
    for (i = j = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 0)
            ca[subsumption_queue[i]].mark(2);

    for (i = 0; i < touched.size(); i++)
        if (touched[i]){
            const vec<CRef>& cs = occurs.lookup(i);
            for (j = 0; j < cs.size(); j++)
                if (ca[cs[j]].mark() == 0){
                    subsumption_queue.insert(cs[j]);
                    ca[cs[j]].mark(2);
                }
            touched[i] = 0;
        }

    for (i = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 2)
            ca[subsumption_queue[i]].mark(0);

    n_touched = 0;
}


bool SimpSolver::implied(const vec<Lit>& c)
{
    assert(decisionLevel() == 0);

    trail_lim.push(trail.size());
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True){
            cancelUntil(0);
            return true;
        }else if (value(c[i]) != l_False){
            assert(value(c[i]) == l_Undef);
            uncheckedEnqueue(~c[i]);
        }

    bool result = propagate() != CRef_Undef;
    cancelUntil(0);
    return result;
}


// Backward subsumption + backward subsumption resolution
bool SimpSolver::backwardSubsumptionCheck(bool verbose)
{
    int cnt = 0;
    int subsumed = 0;
    int deleted_literals = 0;
    assert(decisionLevel() == 0);

    while (subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()){

        // Empty subsumption queue and return immediately on user-interrupt:
        if (asynch_interrupt){
            subsumption_queue.clear();
            bwdsub_assigns = trail.size();
            break; }

        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        if (subsumption_queue.size() == 0 && bwdsub_assigns < trail.size()){
            Lit l = trail[bwdsub_assigns++];
            ca[bwdsub_tmpunit][0] = l;
            ca[bwdsub_tmpunit].calcAbstraction();
            subsumption_queue.insert(bwdsub_tmpunit); }

        CRef    cr = subsumption_queue.peek(); subsumption_queue.pop();
        Clause& c  = ca[cr];

        if (c.mark()) continue;

        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
            printf("c subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        assert(c.size() > 1 || value(c[0]) == l_True);    // Unit-clauses should have been propagated before this point.

        // Find best variable to scan:
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
            if (occurs[var(c[i])].size() < occurs[best].size())
                best = var(c[i]);

        // Search all candidates:
        vec<CRef>& _cs = occurs.lookup(best);
        CRef*       cs = (CRef*)_cs;

        for (int j = 0; j < _cs.size(); j++)
            if (c.mark())
                break;
            else if (!ca[cs[j]].mark() &&  cs[j] != cr && (subsumption_lim == -1 || ca[cs[j]].size() < subsumption_lim)){
	      //  Lit l1 = c.subsumes(ca[cs[j]]);
	      Lit l = simplesubsume(c, ca[cs[j]]);
	      //Lit l = subsume(c, ca[cs[j]]);
	      // assert(l1 == l);
                if (l == lit_Undef)
                    subsumed++, removeClause(cs[j]);
                else if (l != lit_Error){
                    deleted_literals++;

                    if (!strengthenClause(cs[j], ~l))
                        return false;

                    // Did current candidate get deleted from cs? Then check candidate at index j again:
                    if (var(l) == best)
                        j--;
                }
            }
    }

    return true;
}


bool SimpSolver::asymm(Var v, CRef cr)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);

    if (c.mark() || satisfied(c)) return true;

    trail_lim.push(trail.size());
    Lit l = lit_Undef;
    for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v){
            if (value(c[i]) != l_False)
                uncheckedEnqueue(~c[i]);
        }else
            l = c[i];

    if (propagate() != CRef_Undef){
        cancelUntil(0);
        asymm_lits++;
        if (!strengthenClause(cr, l))
            return false;
    }else
        cancelUntil(0);

    return true;
}


bool SimpSolver::asymmVar(Var v)
{
    assert(use_simplification);

    const vec<CRef>& cls = occurs.lookup(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, cls[i]))
            return false;

    return backwardSubsumptionCheck();
}


// static void mkElimClause(vec<uint32_t>& elimclauses, Lit x)
// {
//     elimclauses.push(toInt(x));
//     elimclauses.push(1);
// }


// static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c)
// {
//     int first = elimclauses.size();
//     int v_pos = -1;

//     // Copy clause to elimclauses-vector. Remember position where the
//     // variable 'v' occurs:
//     for (int i = 0; i < c.size(); i++){
//         elimclauses.push(toInt(c[i]));
//         if (var(c[i]) == v)
//             v_pos = i + first;
//     }
//     assert(v_pos != -1);

//     // Swap the first literal with the 'v' literal, so that the literal
//     // containing 'v' will occur first in the clause:
//     uint32_t tmp = elimclauses[v_pos];
//     elimclauses[v_pos] = elimclauses[first];
//     elimclauses[first] = tmp;

//     // Store the length of the clause last:
//     elimclauses.push(c.size());
// }



bool SimpSolver::eliminateVar(Var v)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    // Split the occurrences into positive and negative:
    //
    const vec<CRef>& cls = occurs.lookup(v);
    vec<CRef>        pos, neg;
    for (int i = 0; i < cls.size(); i++)
        (find(ca[cls[i]], mkLit(v)) ? pos : neg).push(cls[i]);

    // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
    // clause must exceed the limit on the maximal clause size (if it is set):
    //
    int cnt         = 0;
    int clause_size = 0;

    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) && 
                (++cnt > cls.size() + grow || (clause_lim != -1 && clause_size > clause_lim)))
                return true;

    // Delete and store old clauses:
    eliminated[v] = true;
    setDecisionVar(v, false);
    eliminated_vars++;

    if (pos.size() > neg.size()){
        for (int i = 0; i < neg.size(); i++)
            mkElimClause(elimclauses, v, ca[neg[i]]);
        mkElimClause(elimclauses, mkLit(v));
    }else{
        for (int i = 0; i < pos.size(); i++)
            mkElimClause(elimclauses, v, ca[pos[i]]);
        mkElimClause(elimclauses, ~mkLit(v));
    }
    // Produce clauses in cross product:
    vec<Lit>& resolvent = add_tmp;
    for (int i = 0; i < pos.size(); i++)
      for (int j = 0; j < neg.size(); j++) {
	int savedCaluses=clauses.size();
	if (merge(ca[pos[i]], ca[neg[j]], v, resolvent) && !addClause_(resolvent))
	  return false;
	else if (clauses.size() == savedCaluses + 1) {nbAllResolvs++;
	  resolvents.push(clauses.last()); }
      }

    for (int i = 0; i < cls.size(); i++)
        removeClause(cls[i]); 

    // Free occurs list for this variable:
    occurs[v].clear(true);
    
    // Free watchers lists for this variable, if possible:
    watches_bin[ mkLit(v)].clear(true);
    watches_bin[~mkLit(v)].clear(true);
    watches[ mkLit(v)].clear(true);
    watches[~mkLit(v)].clear(true);

    return backwardSubsumptionCheck();
}


bool SimpSolver::substitute(Var v, Lit x)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    if (!ok) return false;

    eliminated[v] = true;
    setDecisionVar(v, false);
    const vec<CRef>& cls = occurs.lookup(v);
    
    vec<Lit>& subst_clause = add_tmp;
    for (int i = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];

        subst_clause.clear();
        for (int j = 0; j < c.size(); j++){
            Lit p = c[j];
            subst_clause.push(var(p) == v ? x ^ sign(p) : p);
        }

        if (!addClause_(subst_clause))
            return ok = false;

        removeClause(cls[i]);
    }

    return true;
}


void SimpSolver::extendModel()
{
    int i, j;
    Lit x;

    for (i = elimclauses.size()-1; i > 0; i -= j){
        for (j = elimclauses[i--]; j > 1; j--, i--)
            if (modelValue(toLit(elimclauses[i])) != l_False)
                goto next;

        x = toLit(elimclauses[i]);
        model[var(x)] = lbool(!sign(x));
    next:;
    }
}

// Almost duplicate of Solver::removeSatisfied. Didn't want to make the base method 'virtual'.
void SimpSolver::removeSatisfied()
{
    int i, j;
    for (i = j = 0; i < clauses.size(); i++){
        const Clause& c = ca[clauses[i]];
        if (c.mark() == 0)
            if (satisfied(c))
                removeClause(clauses[i]);
            else
                clauses[j++] = clauses[i];
    }
    clauses.shrink(i - j);
}

// The technique and code are by the courtesy of the GlueMiniSat team. Thank you!
// It helps solving certain types of huge problems tremendously.
bool SimpSolver::eliminate(bool turn_off_elim)
{
  
    bool res = true;
    int iter = 0;
    int n_cls, n_cls_init, n_vars;

    nbUnitViviResolv=0, shortened = 0, nbSimplifing = 0, nbRemovedLits=0;
    saved_s_up = s_propagations;

    if (nVars() == 0) goto cleanup; // User disabling preprocessing.
    if (nClauses()/nVars() > 100) goto cleanup;

    // goto cleanup;

    // Get an initial number of clauses (more accurately).
    if (trail.size() != 0) removeSatisfied();
    n_cls_init = nClauses();
    resolvents.clear();

    res = eliminate_(); // The first, usual variable elimination of MiniSat.
    if (!res) goto cleanup;

    n_cls  = nClauses();
    n_vars = nFreeVars();

    printf("c Reduced to %d vars, %d cls (grow=%d), trail %d\n", n_vars, n_cls, grow, trail.size());

    if ((double)n_cls / n_vars >= 10 || n_vars < 10000){
        printf("c No iterative elimination performed. (vars=%d, c/v ratio=%.1f)\n", n_vars, (double)n_cls / n_vars);
        goto cleanup; }

    grow = grow ? grow * 2 : 8;
    for (; grow < 10000; grow *= 2){
        // Rebuild elimination variable heap.
        for (int i = 0; i < clauses.size(); i++){
            const Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (!elim_heap.inHeap(var(c[j])))
                    elim_heap.insert(var(c[j]));
                else
                    elim_heap.update(var(c[j])); }

        int n_cls_last = nClauses();
        int n_vars_last = nFreeVars();

        res = eliminate_();
        if (!res || n_vars_last == nFreeVars()) break;
        iter++;

        int n_cls_now  = nClauses();
        int n_vars_now = nFreeVars();

        double cl_inc_rate  = (double)n_cls_now   / n_cls_last;
        double var_dec_rate = (double)n_vars_last / n_vars_now;

        printf("c Reduced to %d vars, %d cls (grow=%d), trail %d\n", n_vars_now, n_cls_now, grow, trail.size());
        printf("c cl_inc_rate=%.3f, var_dec_rate=%.3f\n", cl_inc_rate, var_dec_rate);

        if (n_cls_now > n_cls_init || cl_inc_rate > var_dec_rate) break;
    }
    printf("c No. effective iterative eliminations: %d\n", iter);
    printf("c trail before vivification %d\n", trail.size());

    if (res) {
      res = simplifyResolvents();
      printf("c trail after vivification %d\n", trail.size());
      double avgRemovedLits = shortened > 0 ? (double)nbRemovedLits/shortened : 0;
      printf("c resolvents %d, nbSimplifing: %d, nbShortened: %d\n",
	     nbAllResolvs, nbSimplifing, shortened);
      printf("c avgRemovedLits %4.3lf, nbUnits %d, s_up %llu\n",
	     avgRemovedLits, nbUnitViviResolv, s_propagations-saved_s_up);
    }
cleanup:
    touched  .clear(true);
    occurs   .clear(true);
    //   n_occ    .clear(true);
    elim_heap.clear(true);
    subsumption_queue.clear(true);

    use_simplification    = false;
    remove_satisfied      = true;
    ca.extra_clause_field = false;

    // Force full cleanup (this is safe and desirable since it only happens once):
    rebuildOrderHeap();
    garbageCollect();

    if (!res && drup_file)
      fluch2drup(drup_file);
    
    return res;
}


bool SimpSolver::eliminate_()
{
    if (!simplify())
        return false;
    else if (!use_simplification)
        return true;

    int trail_size_last = trail.size();

    // Main simplification loop:
    //
    while (n_touched > 0 || bwdsub_assigns < trail.size() || elim_heap.size() > 0){

        gatherTouchedClauses();
        // printf("  ## (time = %6.2f s) BWD-SUB: queue = %d, trail = %d\n", cpuTime(), subsumption_queue.size(), trail.size() - bwdsub_assigns);
        if ((subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()) && 
            !backwardSubsumptionCheck(true)){
            ok = false; goto cleanup; }

        // Empty elim_heap and return immediately on user-interrupt:
        if (asynch_interrupt){
            assert(bwdsub_assigns == trail.size());
            assert(subsumption_queue.size() == 0);
            assert(n_touched == 0);
            elim_heap.clear();
            goto cleanup; }

	//	elim_heap.clear();
	//	goto cleanup;

        // printf("  ## (time = %6.2f s) ELIM: vars = %d\n", cpuTime(), elim_heap.size());
        for (int cnt = 0; !elim_heap.empty(); cnt++){
            Var elim = elim_heap.removeMin();
            
            if (asynch_interrupt) break;

            if (isEliminated(elim) || value(elim) != l_Undef) continue;

            if (verbosity >= 2 && cnt % 100 == 0)
                printf("c elimination left: %10d\r", elim_heap.size());

            if (use_asymm){
                // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                bool was_frozen = frozen[elim];
                frozen[elim] = true;
                if (!asymmVar(elim)){
                    ok = false; goto cleanup; }
                frozen[elim] = was_frozen; }

            // At this point, the variable may have been set by assymetric branching, so check it
            // again. Also, don't eliminate frozen variables:
            if (use_elim && value(elim) == l_Undef && !frozen[elim] && !eliminateVar(elim)){
                ok = false; goto cleanup; }

            checkGarbage(simp_garbage_frac);
        }

        assert(subsumption_queue.size() == 0);
    }
    
 cleanup:
    // To get an accurate number of clauses.
    if (trail_size_last != trail.size())
        removeSatisfied();
    else{
        int i,j;
        for (i = j = 0; i < clauses.size(); i++)
            if (ca[clauses[i]].mark() == 0)
                clauses[j++] = clauses[i];
        clauses.shrink(i - j);
    }
    checkGarbage();

    if (verbosity >= 1 && elimclauses.size() > 0)
        printf("c |  Eliminated clauses:     %10.2f Mb                                      |\n", 
               double(elimclauses.size() * sizeof(uint32_t)) / (1024*1024));

    return ok;
}

template<class Lits>
void printClause(Lits& ps) {
  for (int i = 0; i < ps.size(); i++)
    printf("%i ", (var(ps[i])) * (-2 * sign(ps[i]) + 1));
  printf("\n");
}

// vars eliminated or fixed at level 0 are removed, so that the other variables
// are made consecutive
void SimpSolver::compactCNF() {
  //make sure that each clause contains only variables not fixed at level 0
  int i, j;
  for(i=0, j=0; i<clauses.size(); i++) {
    CRef cr=clauses[i];
    if (cleanClause(cr)) {
      clauses[j++] = cr;
    }
  }
  clauses.shrink(i-j);

  // for(int v=0; v<nVars(); v++)
  //   repr[v] = v;

  //represent each non-consecutive var by a distinct eliminated or fixed var
  Var v, firstElimV;
  for(v=0, firstElimV=0; v<nVars(); v++) {
    assert(v >= firstElimV);
    if (value(v) != l_Undef) {
      assert(level(v) == 0);
      vardata[v].reason = CRef_Undef;
    }
    Lit p=mkLit(v);
    watches[p].clear();     watches[~p].clear();
    watches_bin[p].clear();     watches_bin[~p].clear();
    reprBy[v] = var_Undef;
    if (!isEliminated(v) && value(v) == l_Undef) {
      if (v>firstElimV) {
	// v will be replaced by firstElimV, i.e., firstElimV will be in the place of v
	savedAssigns[firstElimV] = assigns[firstElimV];
	assigns[firstElimV] = l_Undef; eliminated[firstElimV] = false;
	if (decision[v]) {
	  setDecisionVar(v, false);
	  setDecisionVar(firstElimV, true);
	}
	reprBy[v] = firstElimV; repr[firstElimV] = v;
	eliminated[v]=true;
	polarity[firstElimV]=polarity[v];
	//	printf("%d %d\n", v, firstElimV);
	// if (v==3 || firstElimV==3)
	//   printf("dsfsd ");
      }
      firstElimV++;
    }
    else if (decision[v])
      setDecisionVar(v, false);
  }
  printf("c real number of variables: %d, desisionVars %llu\n", firstElimV, dec_vars);
  realNbVars = firstElimV;
  oriNbVars = nVars();
  vardata.shrink(vardata.size() - firstElimV);
  for(i=0; i<clauses.size(); i++) {
    CRef cr=clauses[i];
    Clause& c=ca[cr];
    // bool changed=false;
    vec<Lit> lits;
    for(int k=0; k<c.size(); k++) lits.push(c[k]);
    // if ( (var(c[0])== 5346 || var(c[1]) == 5346))
    //   printClause(c);
    for(int k=0; k<c.size(); k++) {
      if (reprBy[var(c[k])] != var_Undef) {
	c[k] = mkLit(reprBy[var(c[k])]) ^ sign(c[k]);
	//	changed=true;
      }
    }
    // if (changed) {
    //   printClause(lits);
    //   printClause(c);
    // }
    // printf("\n");
    c.calcAbstraction();
    attachClause(cr);
  }
  rebuildOrderHeap();
  trail.clear(); qhead=0;
}

void SimpSolver::restoreElimValue() {
  model.growTo(oriNbVars);
  for(Var v=oriNbVars-1; v>=nVars(); v--)
    model[v] = assigns[v];
  for(Var v=oriNbVars-1; v>=0; v--)
    if (reprBy[v] != var_Undef) {
      assert(value(v) == l_Undef && reprBy[v] < v);
      assigns[v]=assigns[reprBy[v]];
      model[v] = model[reprBy[v]];
      assigns[reprBy[v]] = savedAssigns[reprBy[v]];
      model[reprBy[v]] = savedAssigns[reprBy[v]];
      eliminated[v] = false;
    }
}

//=================================================================================================
// Garbage Collection methods:
// void SimpSolver::cleanUpClauses()
// {
//     occurs.cleanAll();
//     int i,j;
//     for (i = j = 0; i < clauses.size(); i++)
//         if (ca[clauses[i]].mark() == 0)
//             clauses[j++] = clauses[i];
//     clauses.shrink(i - j);
// }

void SimpSolver::relocAll(ClauseAllocator& to)
{
    if (!use_simplification) return;

    // All occurs lists:
    //
    occurs.cleanAll();
    for (int i = 0; i < nVars(); i++){
        vec<CRef>& cs = occurs[i];
        for (int j = 0; j < cs.size(); j++)
            ca.reloc(cs[j], to);
    }

    // Subsumption queue:
    //
    for (int i = 0; i < subsumption_queue.size(); i++)
        ca.reloc(subsumption_queue[i], to);

    // Temporary clause:
    //
    ca.reloc(bwdsub_tmpunit, to);

    int i, j;
    for(i=j=0; i<resolvents.size(); i++) {
      if (!removed(resolvents[i])) {
	ca.reloc(resolvents[i], to);
	resolvents[j++] = resolvents[i];
      }
    }
    resolvents.shrink(i-j);
}

void SimpSolver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
  
  // ClauseAllocator to(ca.size() - ca.wasted());
  ClauseAllocator to(ca.wasted() > ca.size()/2 ? ca.size()/2 : ca.size() - ca.wasted()); 

    to.extra_clause_field = ca.extra_clause_field; // NOTE: this is important to keep (or lose) the extra fields.
    relocAll(to);
    Solver::relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}





//--------------------------------------------------------------
// SBVA
//--------------------------------------------------------------
void SimpSolver::init_bva() {
    bva.init(nVars(), nClauses());

    for (int i = 0; i < nClauses(); ++i) {
        Clause &cla = ca[clauses[i]];
        for (int j = 0; j < cla.size(); ++j) {
            bva.lit_to_clauses->operator[](toInt(cla[j])).push_back(clauses[i]);
        }
    }
}

void SimpSolver::run_bva() {
    struct pair_op {
        bool operator()(const std::pair<int, int> &a, const std::pair<int, int> &b) {
            return a.first < b.first;
        }
    };

    std::priority_queue<std::pair<int, int>, std::vector<std::pair<int, int>>, pair_op> pq;

    for (int i = 1; i <= nVars(); ++i) {
        pq.push({bva.real_lit_count(i), i});
        pq.push({bva.real_lit_count(-i), -i});
    }

    // int reduce_count = 0;
    while (pq.size() > 0) {
        bva.matched_lits->resize(0);
        bva.matched_clauses->resize(0);
        bva.matched_clauses_id->resize(0);
        bva.clauses_to_remove->resize(0);
        bva.tmp_heuristic_cache_full.clear();

        auto p = pq.top();
        pq.pop();

        int var = p.second;
        int num_matched = p.first;

        // int real_num_matched = real_lit_count(var);
        if (num_matched == 0 || num_matched != bva.real_lit_count(var)) continue;


        Lit lit = (var > 0) ? mkLit(var - 1) : ~mkLit(-var - 1);

        // Mlit := { l }
        bva.matched_lits->push_back(var);

        // Mcls := F[l]
        for (int i = 0; i < (int) bva.lit_to_clauses->operator[](toInt(lit)).size(); ++i) {  
            CRef clause_idx = bva.lit_to_clauses->operator[](toInt(lit))[i];
            
            if (ca[clause_idx].mark() == 0) {
                bva.matched_clauses->push_back(clause_idx);
                bva.matched_clauses_id->push_back(i);
                bva.clauses_to_remove->push_back({clause_idx, i});
            }
        }

        while (1) {
            bva.matched_entries->resize(0);
            bva.matched_entries_lits->resize(0);

            for (int i = 0; i < (int) bva.matched_clauses->size(); ++i) {
                CRef clause_idx = bva.matched_clauses->operator[](i);
                // int clause_id = matched_clauses_id->operator[](i);

                Lit lmin = bva.least_frequent_not(ca[clause_idx], lit);
                if (lmin == lit_Undef) continue;

                // std::cout << toVar(lmin) << std::endl;

                for (CRef other_idx : bva.lit_to_clauses->operator[](toInt(lmin))) {

                    if (ca[other_idx].mark() != 0) continue;
                    if (ca[clause_idx].size() != ca[other_idx].size()) continue;

                    bva.clause_sub(ca[clause_idx], ca[other_idx], 2);

                    if (bva.diff->size() == 1 && bva.diff->operator[](0) == lit) {
                        bva.clause_sub(ca[other_idx], ca[clause_idx], 2); // 首先保证了两个子句的文字数相同，然后进行后续的判断

                        int lelse = toVar(bva.diff->operator[](0)); // 转换成具体文字
                        bool found = false;
                        for (int l : *bva.matched_lits) {
                            if (l == lelse) {
                                found = true;
                                break;
                            }
                        }

                        // if lit not in Mlit then
                        // 如果不在原始文字集，那么放入entries，表示这是一个可能的交集
                        if (!found) {
                            // std::cout << "lelse:" << lelse << std::endl;
                            bva.matched_entries->push_back({lelse, other_idx, i});
                            bva.matched_entries_lits->push_back(lelse);
                        }
                    }
                }
                // exit(0);
            }

            sort(bva.matched_entries_lits->begin(), bva.matched_entries_lits->end());



            // int lmax = 0;
            // int lmax_count = 0;
            // double lamx_act = -1.0;

            // std::vector<std::pair<int, int>> ties;
            // ties.reserve(50);

            // for (int i = 0; i < (int) bva.matched_entries_lits->size();) {
            //     int lelse = bva.matched_entries_lits->operator[](i);
            //     double lelse_act = activity[bva.sparsevec_lit_idx(lelse)];
            //     int count = 0;

            //     while (i < (int) bva.matched_entries_lits->size() && bva.matched_entries_lits->operator[](i) == lelse) {
            //         ++count;
            //         ++i;
            //     }
                
            //     if (count < 2) continue;
                
            //     if (lelse_act > lamx_act) {
            //         lmax = lelse;
            //         lamx_act = lelse_act;
            //         ties.clear();
            //         ties.push_back({lelse, count});
            //     } else if (isEqual(lelse_act, lamx_act)) {
            //         ties.push_back({lelse, count});
            //     }
            // }

            // if (lmax == 0) break;
            
            // std::pair<int, int> p = ties[rand() % ties.size()];
            // lmax = p.first;
            // lmax_count = p.second;

            int lmax = 0;
            int lmax_count = 0;

            std::vector<int> ties;
            ties.reserve(50);

            for (int i = 0; i < (int) bva.matched_entries_lits->size();) {
                int lelse = bva.matched_entries_lits->operator[](i);
                int count = 0;

                while (i < (int) bva.matched_entries_lits->size() && bva.matched_entries_lits->operator[](i) == lelse) {
                    ++count;
                    ++i;
                }

                if (count > lmax_count) {
                    lmax = lelse;
                    lmax_count = count;
                    ties.clear();
                    ties.push_back(lelse);
                } else if (count == lmax_count) {
                    ties.push_back(lelse);
                }
            }

            if (lmax == 0) break;

            int prev_clause_count = bva.matched_clauses->size();
            int prev_lit_count = bva.matched_lits->size();

            int new_clause_count = lmax_count;
            int new_lit_count = prev_lit_count + 1;
            
            int current_reduction = bva.reduction(prev_lit_count, prev_clause_count);
            int new_reduction = bva.reduction(new_lit_count, new_clause_count);
            if (new_reduction <= current_reduction) break;

            // if (ties.size() > 1) {
            //     double cur_act = activity[abs(ties[0]) - 1];
            //     for (int i = 1; i < (int) ties.size(); ++i) {
            //         double tmp = activity[abs(ties[0]) - 1];
            //         if (cur_act < tmp) {
            //             cur_act = tmp;
            //             lmax = ties[i];
            //         }
            //     }
            // }

            if (ties.size() > 1) {
                int max_heuristic_val = bva.tiebreaking_heuristic(ca, var, ties[0]);
                for (int i = 1; i < (int) ties.size(); ++i) {
                    int tmp = bva.tiebreaking_heuristic(ca, var, ties[i]);
                    // std::cout << ties[i] << ", " << tmp << std::endl;
                    if (tmp > max_heuristic_val) {
                        max_heuristic_val = tmp;
                        lmax = ties[i];
                    }
                }
            }

            bva.matched_lits->push_back(lmax);

            bva.matched_clauses_swap->resize(lmax_count);
            bva.matched_clauses_id_swap->resize(lmax_count);

            int insert_idx = 0;
            for (auto pair : *bva.matched_entries) {
                int lelse = std::get<0>(pair);
                if (lelse != lmax) continue;

                CRef cluase_idx = std::get<1>(pair);
                int idx = std::get<2>(pair);

                bva.matched_clauses_swap->operator[](insert_idx) = bva.matched_clauses->operator[](idx);
                bva.matched_clauses_id_swap->operator[](insert_idx) = bva.matched_clauses_id->operator[](idx);
                ++insert_idx;

                bva.clauses_to_remove->push_back({cluase_idx, bva.matched_clauses_id->operator[](idx)});
            }

            std::swap(bva.matched_clauses, bva.matched_clauses_swap);
            std::swap(bva.matched_clauses_id, bva.matched_clauses_id_swap);
        }

        // if (bva.matched_lits->size() <= 1) continue;
        // if (bva.matched_clauses->size() <= 1) continue;
        if (bva.matched_lits->size() == 1) continue;
        if (bva.matched_lits->size() <= 2 && bva.matched_clauses->size() <= 2) continue;

        int matched_clause_count = bva.matched_clauses->size();
        int matched_lit_count = bva.matched_lits->size();

        // 增加文字数量
        newVar();
        bva.num_vars += 1;
        int new_vars = bva.num_vars;

        // 扩充容量
        bva.lit_to_clauses->resize(new_vars * 2);
        bva.lit_count_adjust->resize(new_vars * 2);
        if (bva.sparsevec_lit_idx(new_vars) >= (uint32_t) bva.adjacency_matrix_width) {
            bva.adjacency_matrix_width = new_vars * 2;
            bva.adjacency_matrix.clear();
        }
        bva.adjacency_matrix.resize(new_vars);

        // add (f, lit) clause
        vec<Lit> lits;
        for (int i = 0; i < matched_lit_count; ++i) {
            int parsed_var = bva.matched_lits->operator[](i);

            lits.clear();
            lits.push((parsed_var > 0) ? mkLit(parsed_var - 1) : ~mkLit(-parsed_var - 1));
            lits.push(mkLit(new_vars - 1));

            if (drup_file) {
                writeClause2drup('a', lits, drup_file);
            }

            addClause_(lits);
        }

        // add (-f, ...) clause
        for (int i = 0; i < matched_clause_count; ++i) {
            CRef clause_idx = bva.matched_clauses->operator[](i);
            Clause &cla = ca[clause_idx];

            lits.clear();
            for (int i = 0; i < cla.size(); ++i) {
                if (cla[i] != lit) lits.push(cla[i]);
            }
            lits.push(~mkLit(new_vars - 1));

            if (drup_file) {
                writeClause2drup('a', lits, drup_file);
            }
            
            addClause_(lits);
        }

        // delete clause
        std::set<int> valid_clause_ids;
        for (int i = 0; i < matched_clause_count; i++) {
            valid_clause_ids.insert(bva.matched_clauses_id->operator[](i));
        }

        int remove_clause_count = 0;
        bva.lits_to_update.clear();

        for (auto to_remove : *bva.clauses_to_remove) {
            CRef clause_idx = std::get<0>(to_remove);
            int clause_id = std::get<1>(to_remove);

            if (valid_clause_ids.find(clause_id) == valid_clause_ids.end()) continue;

            Clause &c = ca[clause_idx];
            for (int i = 0; i < c.size(); ++i) {
                Lit lit = c[i];
                bva.lit_count_adjust->operator[](toInt(lit)) -= 1;
                bva.lits_to_update.insert(toVar(lit)); // 记录哪些文字更新了子句
            } 

            if (drup_file) {
                writeClause2drup('d', c, drup_file);
            }
            removeClause(clause_idx);

            ++remove_clause_count;
        }

        bva.total_deleted += remove_clause_count;
        bva.cur_deleted += remove_clause_count;
        bva.num_clauses += matched_lit_count + matched_clause_count; // 没有减去删除的子句个数
        
        for (auto l : bva.lits_to_update) {
            pq.push({bva.real_lit_count(l), l});
            bva.adjacency_matrix[bva.sparsevec_lit_idx(l)] = Eigen::SparseVector<int>(bva.adjacency_matrix_width);
        }
        pq.push({bva.real_lit_count(new_vars), new_vars});
        pq.push({bva.real_lit_count(-new_vars), -new_vars});
        pq.push({bva.real_lit_count(var), var});
    }

    // 清除子句
    // bva.init(nVars(), nClauses());
    // bva.clean_clauses(ca);
    
    bva.lits_to_update.clear();
    if (bva.cur_deleted > 0) {
        // cleanUpClauses(); 
        garbageCollect();
        // printf("----------\n");
    }
}
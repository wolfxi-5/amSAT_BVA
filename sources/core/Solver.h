/****************************************************************************************[Solver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh
 
Maple_LCM, Based on MapleCOMSPS_DRUP -- Copyright (c) 2017, Mao Luo, Chu-Min LI, Fan Xiao: implementing a learnt clause minimisation approach
Reference: M. Luo, C.-M. Li, F. Xiao, F. Manya, and Z. L. , “An effective learnt clause minimization approach for cdcl sat solvers,” in IJCAI-2017, 2017, pp. to–appear.

Maple_LCM_Dist, Based on Maple_LCM -- Copyright (c) 2017, Fan Xiao, Chu-Min LI, Mao Luo: using a new branching heuristic called Distance at the beginning of search

MapleLCMDistChronoBT, based on Maple_LCM_Dist -- Copyright (c), Alexander Nadel, Vadim Ryvchin: "Chronological Backtracking" in SAT-2018, pp. 111-121.

MapleLCMDistChronoBT-DL, based on MapleLCMDistChronoBT -- Copyright (c), Stepan Kochemazov, Oleg Zaikin, Victor Kondratiev, Alexander Semenov: The solver was augmented with heuristic that moves duplicate learnt clauses into the core/tier2 tiers depending on a number of parameters.
 
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

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#define ANTI_EXPLORATION
#define BIN_DRUP

#define GLUCOSE23
//#define INT_QUEUE_AVG
//#define LOOSE_PROP_STAT

#ifdef GLUCOSE23
#define INT_QUEUE_AVG
#define LOOSE_PROP_STAT
#endif

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "utils/Options.h"
#include "core/SolverTypes.h"
#include "utils/ccnr.h"

#include "mtl/BVA.h"

// duplicate learnts version
#include <chrono>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
// duplicate learnts version


// Don't change the actual numbers.
#define LOCAL 0
#define TIER2 2
#define CORE  3

namespace Minisat {

//=================================================================================================
// Solver -- the main class:

class Solver {
private:
    template<typename T>
    class MyQueue {
        int max_sz, q_sz;
        int ptr;
        int64_t sum;
        vec<T> q;
    public:
        MyQueue(int sz) : max_sz(sz), q_sz(0), ptr(0), sum(0) { assert(sz > 0); q.growTo(sz); }
        inline bool   full () const { return q_sz == max_sz; }
#ifdef INT_QUEUE_AVG
        inline T      avg  () const { assert(full()); return sum / max_sz; }
#else
        inline double avg  () const { assert(full()); return sum / (double) max_sz; }
#endif
        inline void   clear()       { sum = 0; q_sz = 0; ptr = 0; }
        void push(T e) {
            if (q_sz < max_sz) q_sz++;
            else sum -= q[ptr];
            sum += e;
            q[ptr++] = e;
            if (ptr == max_sz) ptr = 0;
        }
    };

public:

    // Constructor/Destructor:
    //
    Solver();
    virtual ~Solver();


    vec<Var> reprBy;
    vec<Var> repr;
    
    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

    bool    addClause (const vec<Lit>& ps);                     // Add a clause to the solver.
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (Lit p);                                  // Add a unit clause to the solver.
    bool    addClause (Lit p, Lit q);                           // Add a binary clause to the solver.
    bool    addClause (Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver.
    bool    addClause_(vec<Lit>& ps, bool sadd = true);                     // Add a clause to the solver without making superflous internal copy. Will
    // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
    bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
    bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);
    
    // Variable mode:
    //
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;

    // Resource contraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
    // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    FILE*     drup_file;
    int       verbosity;
    double    step_size;
    double    step_size_dec;
    double    min_step_size;
    int       timer;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      VSIDS;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;


    // duplicate learnts version
    
    uint32_t       min_number_of_learnts_copies;    
    uint32_t       dupl_db_init_size;
    uint32_t       max_lbd_dup;
    std::chrono::microseconds duptime;
    // duplicate learnts version

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts, conflicts_VSIDS;
    uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;
    uint64_t chrono_backtrack, non_chrono_backtrack;


    // duplicate learnts version
    uint64_t duplicates_added_conflicts;
    uint64_t duplicates_added_tier2;
    uint64_t duplicates_added_minimization;    
    uint64_t dupl_db_size;
    
    // duplicate learnts version

    vec<uint32_t> picked;
    vec<uint32_t> conflicted;
    vec<uint32_t> almost_conflicted;
#ifdef ANTI_EXPLORATION
    vec<uint32_t> canceled;
#endif

protected:

    // Helper structures:
    //
    struct VarData { CRef reason; int level; int index;};
    static inline VarData mkVarData(CRef cr, int l, int i){ VarData d = {cr, l, i}; return d; }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };
    
    struct ConflictData
	{
		ConflictData() :
			nHighestLevel(-1),
			bOnlyOneLitFromHighest(false)
		{}

		int nHighestLevel;
		bool bOnlyOneLitFromHighest;
	};

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts_core,     // List of learnt clauses.
    learnts_tier2,
    learnts_local;
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity_CHB,     // A heuristic measurement of the activity of a variable.
    activity_VSIDS;
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
    watches_bin,      // Watches for binary clauses only.
    watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<lbool>          assigns;          // The current assignments.
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap_CHB,   // A priority queue of variables ordered with respect to the variable activity.
    order_heap_VSIDS;
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    int                 core_lbd_cut;
    float               global_lbd_sum;
    MyQueue<int>        lbd_queue;  // For computing moving averages of recent LBD values.

    uint64_t            next_T2_reduce,
    next_L_reduce;

    ClauseAllocator     ca;
    
    // duplicate learnts version    
    std::map<int32_t,std::map<uint32_t,std::unordered_map<uint64_t,uint32_t>>>  ht;
  
    // duplicate learnts version

    int 				confl_to_chrono;
    int 				chrono;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;
    vec<Lit>            add_oc;

    vec<uint64_t>       seen2;    // Mostly for efficient LBD computation. 'seen2[i]' will indicate if decision level or variable 'i' has been seen.
    uint64_t            counter;  // Simple counter for marking purpose with 'seen2'.

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, int level = 0, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int& nof_conflicts);                                    // Search for a given number of conflicts.
    lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     reduceDB_Tier2   ();
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     safeRemoveSatisfied(vec<CRef>& cs, unsigned valid_mark);
    void     rebuildOrderHeap ();
    bool     binResMinimize   (vec<Lit>& out_learnt);                                  // Further learnt clause minimization by binary resolution.

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double mult);    // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll         (ClauseAllocator& to);

// duplicate learnts version
    int     is_duplicate     (std::vector<uint32_t>&c); //returns TRUE if a clause is duplicate
// duplicate learnts version

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    
    ConflictData FindConflictLevel(CRef cind);
    
public:
    int      level            (Var x) const;
protected:
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;

    template<class V> int computeLBD(const V& c) {
        int lbd = 0;

        counter++;
        for (int i = 0; i < c.size(); i++){
            int l = level(var(c[i]));
            if (l != 0 && seen2[l] != counter){
                seen2[l] = counter;
                lbd++; } }

        return lbd;
    }

#ifdef BIN_DRUP
    //removed static in all the bin_drup functions below
    static int buf_len;
    static unsigned char drup_buf[];
    static unsigned char* buf_ptr;
    
    inline void byteDRUP(Lit l){
      unsigned int u = 2 * (repr[var(l)] + 1) + sign(l);
      do{
	*buf_ptr++ = u & 0x7f | 0x80; buf_len++;
	u = u >> 7;
      }while (u);
      *(buf_ptr - 1) &= 0x7f; // End marker of this unsigned number.
    }
    
    template<class V>
      inline void binDRUP(unsigned char op, const V& c, FILE* drup_file){
      assert(op == 'a' || op == 'd');

      //   if (op == 'd' && c[0]
      
      *buf_ptr++ = op; buf_len++;
      for (int i = 0; i < c.size(); i++) byteDRUP(c[i]);
      *buf_ptr++ = 0; buf_len++;
      if (buf_len > 1048576) binDRUP_flush(drup_file);
    }
    
    inline void binDRUP_strengthen(const Clause& c, Lit l, FILE* drup_file){
      *buf_ptr++ = 'a'; buf_len++;
      for (int i = 0; i < c.size(); i++)
	if (c[i] != l) byteDRUP(c[i]);
      *buf_ptr++ = 0; buf_len++;
      if (buf_len > 1048576) binDRUP_flush(drup_file);
    }
    
    inline void binDRUP_flush(FILE* drup_file){
      fwrite(drup_buf, sizeof(unsigned char), buf_len, drup_file);
      //  fwrite_unlocked(drup_buf, sizeof(unsigned char), buf_len, drup_file);
      buf_ptr = drup_buf; buf_len = 0;
    }
#endif

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }


    // simplify
    //
public:
    bool	simplifyAll();
    void	simplifyLearnt(Clause& c);
    bool	simplifyLearnt_x(vec<CRef>& learnts_x);
    bool	simplifyLearnt_core();
    bool	simplifyLearnt_tier2();
    int		trailRecord;
    void	litsEnqueue(int cutP, Clause& c);
    void	cancelUntilTrailRecord();
    void	simpleUncheckEnqueue(Lit p, CRef from = CRef_Undef);
    CRef    simplePropagate();
    uint64_t nbSimplifyAll;
    uint64_t simplified_length_record, original_length_record;
    uint64_t s_propagations;

    vec<Lit> simp_learnt_clause;
    vec<CRef> simp_reason_clause;
    void	simpleAnalyze(CRef confl, vec<Lit>& out_learnt, vec<CRef>& reason_clause, bool True_confl);

    // in redundant
    bool removed(CRef cr);
    // adjust simplifyAll occasion
    long curSimplify;
    int nbconfbeforesimplify;
    int incSimplify;

    vec<Var> testedVars;
    vec<Lit> impliedLits;

    void cancelUntilTrailRecord1();
    void cancelUntilTrailRecord2();
    bool failedLiteralDetection0(int limit);

private:
    //  to avoid the init_soln of two LS too near.  
    int     restarts_gap        = 300;
    int     restarts_basic      = 300;
    //  if trail.size() over c*nVars or p*max_trail, call ls.
    // float   conflict_ratio      = 0.4;
    // float   percent_ratio       = 0.9;
    // //  control ls time total use.
    // float   up_time_ratio       = 0.2;
    //  control ls memory use per call.
    long long ls_mems_num       = 50*1000*1000;
    //  whether the mediation_soln is used as rephase, if not 
    // bool    mediation_used      = false;
    
    int     switch_heristic_mod = 500;//starts
    int     last_switch_conflicts;

    //informations 
    // bool    lssolver_constructed = false;
    CCAnr  *lssolver;
    int     freeze_ls_restart_num   = 0;
    double  ls_used_time            = 0;
    int     ls_call_num             = 0;
    int     ls_best_unsat_num       = INT_MAX;
    bool    solved_by_ls            = false;
    int     max_trail               = 0;
    bool    max_trail_improved      = false;
    int     up_build_num            = 0;
    double  up_build_time           = 0.0;

    //Phases
    // save the recent ls soln and best ls soln, need to call ls once.
    char* ls_mediation_soln; 
    // with the minimum unsat clauses num in LS.
    char* ls_best_soln;
    // hold the soln with the best trail size.
    char* top_trail_soln;
    char* tmp_up_build_soln;
    

    //functions 
    // bool    call_ls(bool use_up_build);
    bool    ccanr_has_constructed = false;
    enum    build_type{current_UP,top_trail_UP,random_build};
    bool    call_ls(build_type type);
    void    load_ls_data();
    void    build_soln_with_UP();
    void    rand_based_rephase();
    void    info_based_rephase();

 public:

    Lit get1UIP(CRef confl);

    vec<Lit> learnt_clause, lits2fix, litsForImpliedLits, learntContents;
    vec<CRef> auxiLearnts;
    vec<int> pathCs;
    int tier2_lbd_cut;
    
    bool failedLiteralDetection(int maxNoFail);
    void simpleRemoveLearnts(vec<CRef>& learnts);
    bool learnFromConflict(CRef confl);
    bool propagateImpliedLits(vec<Lit>& impliedLits, Lit testedLit);
    void analyzeImplication(Lit impliedLit, vec<Lit>& out_learnt);
    void simplifyQuasiConflictClause(vec<Lit>&learnt_clause, int& btlevel, int& lbd);
    void myAnalyze(CRef confl, vec<Lit>& learnt_clause, int& backtrack_level, int& lbd);
    CRef LHconfl;
    //  int tier2_lbd_cut;
    
    void getAllUIP(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);

    int trailIndex(Var x) const;

    void simplereduceClause(CRef cr, int pathC);
    int nbFlyReduced;

        /* Queue<CRef>         subsumptionQueue; */
    vec<CRef>         subsumptionQueue;
    // Temporaries:
    //
    CRef                bwdsub_tmpunit;

    struct ClauseDeleted {
      const ClauseAllocator& ca;
      explicit ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
      bool operator()(const CRef& cr) const { return ca[cr].mark() == 1; } };
    
    OccLists<Var, vec<CRef>, ClauseDeleted>
      occurIn;

    void removeClauseFromOccur(CRef dr, bool strict=false);
    void collectClauses(vec<CRef>& clauseSet, int learntType=CORE);
    bool simpleStrengthenClause(CRef cr, Lit l);
    bool subsumeClauses(CRef cr, int& subsumed, int& deleted_literals);
    bool backwardSubsume();
    bool backwardSubsume_(int& savedTrailSize, bool verbose=true);
    bool cleanClause(CRef cr);
    void purgeClauses(vec<CRef>& cs);

   //inpreprocessing variable elimination
    bool eliminate();
    bool eliminate_();
    bool eliminateVar(Var v, int& savedTrailSize);
    void buildElimHeap();
    struct ElimLt {
      const vec<int>& n_occ;
      explicit ElimLt(const vec<int>& no) : n_occ(no) {}
      
      // TODO: are 64-bit operations here noticably bad on 32-bit platforms? Could use a saturating
      // 32-bit implementation instead then, but this will have to do for now.
      uint64_t cost  (Var x)        const { return (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]; }
      bool operator()(Var x, Var y) const { return cost(x) < cost(y); }
    };

    vec<bool>           touched, eliminated;
    vec<Var>            touchedVars;
    vec<Var>            eliminatedVars;
    vec<int>            n_occ;
    Heap<ElimLt>        elim_heap;
    // vec<Lit>           elimclauses;
    vec<uint32_t>      elimclauses;
    vec<bool>          frozen;
    int                 grow;
    int clause_limit;
    void collectOriginalClauses(vec<CRef>& clauseSet);
    static void storeElimClause(vec<Lit>& elimclauses, Var v, Clause& c);
    bool merge(const Clause& _ps, const Clause& _qs, Var v, int& size);
    bool merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    void removeClauseForElim(CRef cr);
    static void mkElimClause(vec<uint32_t>& elimclauses, Lit x);
    static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c);
    void extendModel();
    bool addClauseByResolution(vec<Lit>& ps, int lbd=0);
    void gatherTouchedClauses();
    //    void eliminateLearntClausesContainingElimVar(vec<CRef>& learnts);
    bool isEliminated(Var v);
    void updateElimHeap(Var v);
    void checkGarbageForElimVars();
    int initTrail;

    vec<CRef> resolvents;
    bool simplifyResolvents();
    vec<int> litTrail;

    void cancelUntilTrailRecord2(Lit p, int& nbeq);
    vec<Lit> rpr;
    Lit getRpr(Lit p);
    int nbEqUse, prevEquivLitsNb;
    vec<Lit> equivLits;
    bool eliminateEqLit(CRef cr, Var v, Var targetV);
    bool eliminateEqLits_(int& debut);
    bool eliminateEqLits();
    bool extendEquivLitValue(int debut, bool all=true);

    Lit subsume(const Clause& c, const Clause& d);
    bool myAddClause_(vec<Lit>& ps, CRef& cr, int lbd=0);

    int nbUnitResolv=0, nbUnitViviResolv=0, shortened = 0, nbSimplifing = 0, nbRemovedLits=0, nbAllResolvs=0;
    uint64_t saved_s_up=0;

    void collectLocalClauses(vec<CRef>& clauseSet);
    OccLists<Var, vec<CRef>, ClauseDeleted>
      occurInLocal;

    bool cleanClause(CRef cr, int level0Trail);
    void cancelUntilRecord(int record);
    bool propagateClauseAndAnalyze0(CRef cr, Var v, vec<Lit>& propagatedLits);
    bool propagateClauseAndAnalyze1(CRef cr, Var v, vec<Lit>& propagatedLits, bool& ttlg);
    bool cancelAndPropagateLitClause(Lit p, CRef cr, Var v, vec<Lit>& resolvent);
    bool crossResolvents(vec<CRef>& pos, vec<CRef>& neg, Var v);
    void getWatchedLits(vec<Lit>& resolvent);

    void mySimpleAnalyze(CRef confl, vec<Lit>& out_learnt, bool True_confl);
    int nbRemovedClausesByElim=0, nbSavedResolv=0, nb1stClauseSimp=0;
    
    int sbsmTtlg=0, sbsmAbsFail=0, allsbsm=0;
    double totalelimTime, totalsbsmTime, totalFLtime;
    uint64_t ticks=0, s_ticks=0;
    int nbElim=0, nbLearntResolvs=0, nb1stClauseSimpL=0, nbSavedResolvL=0;
    bool crossResolventsL(vec<CRef>& posL, vec<CRef>& negL, Var v);
    bool elimEqBackWardSubsume();
    bool isSubsumed(vec<Lit>& resolvent, bool learnt=false);
    int sbsmRslv, delLitRslv;
    bool isSubsumed(CRef dr);
    int realNbVars, oriNbVars;
    int smeq=0;
    bool simplesubsumeClauses(CRef cr, int& subsumed, int& deleted_literals);
    bool simplebackwardSubsume_(int& savedTrailSize, bool verbose=true);
    Lit simplesubsume(const Clause& c, const Clause& d);

    struct LocalAct {
      CRef cr;
      double act;
      //  LocalAct(CRef cr_, double act_) : cr(cr_), act(act_) {}
    };

    inline LocalAct mkLocalAct(CRef cr_, double act_) {LocalAct la; la={cr_, act_}; return la;}
    
    vec<LocalAct> localActivity;
    vec<int> localIndex;
    void sortClausesByVarActs(vec<CRef>& cs, vec<double>& activity, unsigned learntType);

    struct localAct_lt {
      //vec<int>& localIndex;
      vec<LocalAct>& localActivity;
    localAct_lt(vec<LocalAct>& localActivity_) : localActivity(localActivity_) {}
      bool operator () (int i, int j) const { return localActivity[i].act < localActivity[j].act; }
    };

    Lit simplePickBranchLit();
    CRef simplePropagateEq();
    //  vec<Lit> reasonLit;

    template<class V> void writeClause2drup(unsigned char op, const V& c,  FILE* drup_file) {
      
#ifdef BIN_DRUP
      binDRUP(op, c, drup_file);
#else
      if (op == 'd')
	fprintf(drup_file, "d ");
      for (int i = 0; i < c.size(); i++)
	fprintf(drup_file, "%i ", (repr[var(c[i])] + 1) * (-2 * sign(c[i]) + 1));
      fprintf(drup_file, "0\n");

      /* // 572 154 3254 -775 -10 -684 589 3339 3338 3203 3202 3253 5901 4733 0 */
      /* if (op == 'a' && c.size() == 2 */
      /* 	  && (repr[var(c[0])] + 1) * (-2 * sign(c[0]) + 1) == 5985  */
      /* 	  && (repr[var(c[1])] + 1) * (-2 * sign(c[1]) + 1) == 5933 ) { */
      /* 	  //  && (repr[var(c[2])] + 1) * (-2 * sign(c[2]) + 1) == 3254 //) { */
      /* 	  //&& (repr[var(c[3])] + 1) * (-2 * sign(c[3]) + 1) == -775) { */
      /* 	printf("000000000000000000000000000000000000000000000000000\n "); */
      /* 	for (int i = 0; i < c.size(); i++) */
      /*      printf("%i ", (repr[var(c[i])] + 1) * (-2 * sign(c[i]) + 1)); */
      /* 	 printf("0\n"); */
      /* } */

      /* if (op == 'd' && c.size() ==2 */
      /* 	  && (repr[var(c[0])] + 1) * (-2 * sign(c[0]) + 1) == 5933 */
      /* 	  && (repr[var(c[1])] + 1) * (-2 * sign(c[1]) + 1) == 5985) { */
      /* 	//	&& (repr[var(c[2])] + 1) * (-2 * sign(c[2]) + 1) == -14193) { */
      /* 	printf("===================================================\n "); */
      /* 	for (int i = 0; i < c.size(); i++) */
      /*      printf("%i ", (repr[var(c[i])] + 1) * (-2 * sign(c[i]) + 1)); */
      /* 	 printf("0\n"); */
      /* } */
#endif
    }

    
    template<class V> void strengthenClause2drup(const V& c,  Lit l, FILE* drup_file) {
#ifdef BIN_DRUP
        binDRUP_strengthen(c, l, drup_file);
#else
        for (int i = 0; i < c.size(); i++)
            if (c[i] != l) fprintf(drup_file, "%i ", (repr[var(c[i])] + 1) * (-2 * sign(c[i]) + 1));
        fprintf(drup_file, "0\n");

	if (c.size() == 2 && (repr[var(c[0])] + 1) * (-2 * sign(c[0]) + 1) == -275 &&
	    (repr[var(c[1])] + 1) * (-2 * sign(c[1]) + 1) == 4) {
	    // && (repr[var(c[2])] + 1) * (-2 * sign(c[2]) + 1) == 13809) {
	  printf("££££££££££££££££££££££££££££££££££££££££££££££££££££££\nd ");
	  for (int i = 0; i < c.size(); i++)
            if (c[i] != l) printf("%i ", (repr[var(c[i])] + 1) * (-2 * sign(c[i]) + 1));
	  printf("0\n");
	}	  
#endif
    }

    void fluch2drup(FILE* drup_file) {
#ifdef BIN_DRUP
      binDRUP_flush(drup_file);
      return;
#else
      return;
#endif
    }

    void writeEmptyClause2drup(FILE* drup_file) {
#ifdef BIN_DRUP
      fputc('a', drup_file); fputc(0, drup_file);
#else
      fprintf(drup_file, "0\n");
#endif
    }
    
    bool notimpbin(Lit p, Lit q); //check if there is a binary clause ~p v q
    int nbEqBin;
    bool propagateTwoLits(Lit p, Lit q);

public:
    BVA bva;

    virtual void init_bva() {printf("init_bva\n");}
    virtual void run_bva() {printf("run_bva\n");}

    void solver_init_bva();
    void solver_run_bva();

    bool isEqual(double x, double y);
};

inline bool Solver::isEqual(double x, double y) {
  return std::fabs(x - y) <= 1e-6;
}


//=================================================================================================
// Implementation of inline methods:

  inline Lit Solver::simplesubsume(const Clause& c, const Clause& d) {
   //  allsbsm++;
   if ((c.size() > d.size()) || ((c.abstraction() & ~d.abstraction()) !=0))
      return lit_Error;
   Lit ret = lit_Undef;
   counter++;
   for(int i=0; i<d.size(); i++)
     seen2[toInt(d[i])]=counter;
   
   for(int i=0; i<c.size(); i++) {
     if (seen2[toInt(~c[i])] == counter) {
       if (ret == lit_Undef)
	 ret = c[i];
       else {
	 sbsmTtlg++;
	 return lit_Error;
       }
     }
     else if (seen2[toInt(c[i])] != counter) {
       sbsmAbsFail++;
       return lit_Error;
     }
   }
   return ret;
 }

  inline Lit Solver::subsume(const Clause& c, const Clause& d) {
   //  allsbsm++;
   if ((c.size() > d.size()) || ((c.abstraction() & ~d.abstraction()) !=0))
      return lit_Error;
   Lit ret = lit_Undef;
   counter++;
   for(int i=0; i<d.size(); i++)
     seen2[toInt(d[i])]=counter;
   
   for(int i=0; i<c.size(); i++) {
     if (seen2[toInt(~c[i])] == counter) {
       if (ret == lit_Undef)
 	 ret = c[i];
       else {
 	 sbsmTtlg++;
 	 if (d.size()==2) {
 	   assert(c.size() == 2);
 	   Lit p=getRpr(d[0]);
 	   Lit q=getRpr(d[1]);
 	   if (var(p) != var(q)) {
 	     smeq++;
 	     rpr[toInt(q)] = ~p;
 	     rpr[toInt(~q)] = p;

	     if (drup_file) {
	       vec<Lit> lits;
	       lits.push(p); lits.push(q);
	       writeClause2drup('a', lits, drup_file);
	       lits[0] = ~p; lits[1] = ~q;
	       writeClause2drup('a', lits, drup_file);
	     }

	     /* if (drup_file && (p != d[0] || q != d[1])) { */
	     /*   vec<Lit> lits1, lits2; */
	     /*   lits1.push(~q), lits1.push(~p);  lits2.push(q), lits2.push(p); */
	     /*   writeClause2drup('a', lits1, drup_file); */
	     /*   writeClause2drup('a', lits2, drup_file); */
	     /* } */
	     
	     /* 	if (equivLits.size() == 2798) */
	     /* 	  printf("&&&&&&&& "); */
	     
 	     equivLits.push(q);
 	   }
 	 }
 	 return lit_Error;
       }
     }
     else if (seen2[toInt(c[i])] != counter) {
       sbsmAbsFail++;
       return lit_Error;
     }
   }
   return ret;
 }

 /* inline Lit Solver::subsume(const Clause& c, const Clause& d) { */
 /*   //  allsbsm++; */
 /*   if ((c.size() > d.size()) || ((c.abstraction() & ~d.abstraction()) !=0)) */
 /*      return lit_Error; */
 /*   Lit ret = lit_Undef; */
 /*   counter++; */
 /*   for(int i=0; i<d.size(); i++) */
 /*     seen2[toInt(d[i])]=counter; */
   
 /*   for(int i=0; i<c.size(); i++) { */
 /*     if (seen2[toInt(~c[i])] == counter) { */
 /*       if (ret == lit_Undef) */
 /* 	 ret = c[i]; */
 /*       else { */
 /* 	 sbsmTtlg++; */
 /* 	 return lit_Error; */
 /*       } */
 /*     } */
 /*     else if (seen2[toInt(c[i])] != counter) { */
 /*       sbsmAbsFail++; */
 /*       return lit_Error; */
 /*     } */
 /*   } */
 /*   return ret; */
 /* } */

  inline void Solver::updateElimHeap(Var v) {
    // if (!frozen[v] && !isEliminated(v) && value(v) == l_Undef)
    if (elim_heap.inHeap(v) || (!frozen[v] && !isEliminated(v) && value(v) == l_Undef))
        elim_heap.update(v); }

   inline bool Solver::isEliminated(Var v) {return eliminated[v];}

inline CRef Solver::reason(Var x) const { return vardata[x].reason; }
inline int  Solver::level (Var x) const { return vardata[x].level; }
 inline int Solver::trailIndex(Var x) const {return vardata[x].index;}

inline void Solver::insertVarOrder(Var x) {
    //    Heap<VarOrderLt>& order_heap = VSIDS ? order_heap_VSIDS : order_heap_CHB;
    Heap<VarOrderLt>& order_heap = ((!VSIDS)? order_heap_CHB:order_heap_VSIDS);
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() {
    var_inc *= (1 / var_decay); }

inline void Solver::varBumpActivity(Var v, double mult) {
    if ( (activity_VSIDS[v] += var_inc * mult) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity_VSIDS[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap_VSIDS.inHeap(v)) order_heap_VSIDS.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity (Clause& c) {
    if ( (c.activity() += cla_inc) > 1e20 ) {
        // Rescale:
      int i, j;
      for (i = j = 0; i < learnts_local.size(); i++) {
	CRef cr = learnts_local[i];
	if (ca[cr].mark() == LOCAL) {
	  ca[cr].activity() *= 1e-20;
	  learnts_local[j++] = cr;
	}
      }
      learnts_local.shrink(i - j);
      cla_inc *= 1e-20; } }

inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, decisionLevel(), from), true); }
inline bool     Solver::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline bool     Solver::locked          (const Clause& c) const {
    int i = c.size() != 2 ? 0 : (value(c[0]) == l_True ? 0 : 1);
    return value(c[i]) == l_True && reason(var(c[i])) != CRef_Undef && ca.lea(reason(var(c[i]))) == &c;
}
inline void     Solver::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    Solver::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nLearnts      ()      const   { return learnts_core.size() + learnts_tier2.size() + learnts_local.size(); }
 inline int      Solver::nVars         ()      const   { return vardata.size(); }
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     Solver::setDecisionVar(Var v, bool b) 
{ 
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    if (b && !order_heap_CHB.inHeap(v)){
        order_heap_CHB.insert(v);
        order_heap_VSIDS.insert(v);}
}
inline void     Solver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver::interrupt(){ asynch_interrupt = true; }
inline void     Solver::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     Solver::withinBudget() const {
    return !asynch_interrupt &&
            (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
            (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     Solver::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     Solver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    Solver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

inline void     Solver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }

//=================================================================================================
// Debug etc:


//=================================================================================================
}

#endif

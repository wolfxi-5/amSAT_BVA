#include "core/Solver.h"
#include "mtl/Sort.h"
#include "utils/System.h"

using namespace Minisat;

bool Solver::isSubsumed(vec<Lit>& resolvent, bool learnt) {
  uint32_t abstraction = 0;
  Var best = var(resolvent[0]);
  counter++;
  seen2[toInt(resolvent[0])]=counter;
  abstraction |= 1 << (var(resolvent[0]) & 31);
  
  for (int i = 1; i < resolvent.size(); i++) {
    Lit lit=resolvent[i];
    if (occurIn[var(lit)].size() < occurIn[best].size())
      best = var(lit);
    abstraction |= 1 << (var(lit) & 31);
    seen2[toInt(lit)]=counter;
  }
 
  vec<CRef>& cs = occurIn[best];
  int j;
  for (j = 0; j < cs.size(); j++) {
    CRef cr=cs[j];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    if ((!learnt && c.learnt()) ||
	(c.size() > resolvent.size()) ||
	((c.abstraction() & (~abstraction)) !=0))
      continue;
    Lit ret = lit_Undef;
    for(int i=0; i<c.size(); i++) {
      //if (seen2[toInt(~c[i])] == counter) {
      // 	if (ret == lit_Undef)
      // 	  ret = c[i];
      // 	else {
      // 	  // sbsmTtlg++;
      // 	  ret = lit_Error;
      // 	  break;
      // 	}
      // }
      // else
      if (seen2[toInt(c[i])] != counter) {
	//sbsmAbsFail++;
	ret = lit_Error;
	break;
      }
    }
    if (ret == lit_Undef) {
      // if (!learnt && c.learnt()) {
      // 	continue;
      // 	// if (resolvent.size() > c.size()) {
      // 	//   for(int k=0; k<c.size(); k++)
      // 	//     resolvent[k]=c[k];
      // 	//   resolvent.shrink(resolvent.size() - c.size());
      // 	//   // abstraction = 0; counter++;
      // 	//   // for (int i = 0; i < resolvent.size(); i++) {
      // 	//   //   Lit lit=resolvent[i];
      // 	//   //   abstraction |= 1 << (var(lit) & 31);
      // 	//   //   seen2[toInt(lit)]=counter;
      // 	//   // }
      // 	// }
      // 	// removeClause(cr);  removeClauseFromOccur(cr, true);
      // 	// return false;
      // }
      // else {
	sbsmRslv++;
	return true;
	// }
    }
    // else if (ret != lit_Error) {
    //   delLitRslv++;
    //   remove(resolvent, ~ret);
    //   if (resolvent.size() == 1)
    // 	return false;
    //   abstraction = 0; counter++;
    //   for (int i = 0; i < resolvent.size(); i++) {
    // 	Lit lit=resolvent[i];
    // 	abstraction |= 1 << (var(lit) & 31);
    // 	seen2[toInt(lit)]=counter;
    //   }
    // }
  }
  return false;
}

void Solver::gatherTouchedClauses() {
  
    if (touchedVars.size() == 0) return;

    int i,j;
    for (i = j = 0; i < subsumptionQueue.size(); i++)
        if (ca[subsumptionQueue[i]].mark() == 0)
            ca[subsumptionQueue[i]].mark(2);

    for (i = 0; i < touchedVars.size(); i++) {
      Var v=touchedVars[i];
      const vec<CRef>& cs = occurIn.lookup(v);
      for (j = 0; j < cs.size(); j++)
	if (ca[cs[j]].mark() == 0){
	  subsumptionQueue.push(cs[j]);
	  ca[cs[j]].mark(2);
	}
      touched[v] = 0;
    }
    touchedVars.clear();

    for (i = 0; i < subsumptionQueue.size(); i++)
        if (ca[subsumptionQueue[i]].mark() == 2)
            ca[subsumptionQueue[i]].mark(0);
}

template<class Lits>
void printClause(Lits& ps) {
  for (int i = 0; i < ps.size(); i++)
    printf("%i ", (var(ps[i])) * (-2 * sign(ps[i]) + 1));
  printf("\n");
}

bool Solver::myAddClause_(vec<Lit>& ps, CRef& cr, int lbd) {
  cr = CRef_Undef;
  
  if (drup_file){
    writeClause2drup('a', ps, drup_file);
// #ifdef BIN_DRUP
//     binDRUP('a', ps, drup_file);
// #else
//     for (int i = 0; i < ps.size(); i++)
//       fprintf(drup_file, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
//     fprintf(drup_file, "0\n");
// #endif
  }
  if (ps.size() == 0)
    return ok = false;
  else if (ps.size() == 1){
    uncheckedEnqueue(ps[0]);
    return ok = (propagate() == CRef_Undef);
  }else{
    cr = ca.alloc(ps, lbd>0);
    if (lbd>0) {
      ca[cr].set_lbd(lbd);
      int  id = 0;                      
      std::vector<uint32_t> tmp;
      for (int i = 0; i < ps.size(); i++)
	tmp.push_back(ps[i].x);
      id = is_duplicate(tmp);             
      if (id == min_number_of_learnts_copies +1){
	duplicates_added_conflicts++;                        
      }                    
      if (id == min_number_of_learnts_copies){
	duplicates_added_tier2++;
      }                                        
      //duplicate learnts
      if ((lbd <= core_lbd_cut) || (id == min_number_of_learnts_copies+1)){
	learnts_core.push(cr);
	ca[cr].mark(CORE);
      }else if ((lbd <= 6)||(id == min_number_of_learnts_copies)){
	learnts_tier2.push(cr);
	ca[cr].mark(TIER2);
	ca[cr].touched() = conflicts;
      }else{
	learnts_local.push(cr);
	claBumpActivity(ca[cr]);
      }
    }
    else 
      clauses.push(cr);
    attachClause(cr);
  }
  return true;
}

// lbd>0 means that this is a learnt clause with lbd
bool Solver::addClauseByResolution(vec<Lit>& ps, int lbd) {
#ifndef NDEBUG
    for (int i = 0; i < ps.size(); i++)
        assert(!isEliminated(var(ps[i])));
#endif

    if (ps.size() > 1) {
      if (isSubsumed(ps, lbd>0))
	return true;
      // else if (ps.size() == 1 && value(ps[0]) != l_Undef) {
      // 	add_tmp.push(ps[0]);
      // 	return true;
      // }
    }
    
    int savedTrail=trail.size();
    CRef cr;
    if (!myAddClause_(ps, cr, lbd))
        return false;
    if (trail.size() - savedTrail > 0) {
      nbUnitResolv++;
      //printf("**** unit clause produced by resolution****\n");
      //printClause(ps);
    }
    if (cr != CRef_Undef){
      const Clause& c  = ca[cr];
      // NOTE: the clause is added to the queue immediately and then
      // again during 'gatherTouchedClauses()'. If nothing happens
      // in between, it will only be checked once. Otherwise, it may
      // be checked twice unnecessarily. This is an unfortunate
      // consequence of how backward subsumption is used to mimic
      // forward subsumption.
      if (lbd > 0)
	nbLearntResolvs++;
      else
	nbAllResolvs++;
      if (lbd<=6) {
	resolvents.push(cr);  subsumptionQueue.push(cr);
	for (int i = 0; i < c.size(); i++){
	  occurIn[var(c[i])].push(cr);
	  if (lbd==0)
	    n_occ[toInt(c[i])]++;
	  litTrail[toInt(~c[i])] = trail.size();
	  if (touched[var(c[i])] == 0) {
	    touched[var(c[i])] = 1;
	    touchedVars.push(var(c[i]));
	  }
	  if (lbd==0 && elim_heap.inHeap(var(c[i])))
	    elim_heap.increase(var(c[i]));
	}
      }
      else
	for (int i = 0; i < c.size(); i++){
	  occurInLocal[var(c[i])].push(cr);
	}
    }
    return true;
}

void Solver::mkElimClause(vec<uint32_t>& elimclauses, Lit x)
{
    elimclauses.push(toInt(x));
    elimclauses.push(1);
}


void Solver::mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c)
{
    int first = elimclauses.size();
    int v_pos = -1;

    // Copy clause to elimclauses-vector. Remember position where the
    // variable 'v' occurs:
    for (int i = 0; i < c.size(); i++){
        elimclauses.push(toInt(c[i]));
        if (var(c[i]) == v)
            v_pos = i + first;
    }
    assert(v_pos != -1);

    // Swap the first literal with the 'v' literal, so that the literal
    // containing 'v' will occur first in the clause:
    uint32_t tmp = elimclauses[v_pos];
    elimclauses[v_pos] = elimclauses[first];
    elimclauses[first] = tmp;

    // Store the length of the clause last:
    elimclauses.push(c.size());
}

void Solver::extendModel()
{
    int i, j;
    Lit x;

    for (i = elimclauses.size()-1; i > 0; i -= j){
        for (j = elimclauses[i--]; j > 1; j--, i--)
	  if (value(getRpr(toLit(elimclauses[i]))) != l_False)
                goto next;

	//  x = toLit(elimclauses[i]);
	x = getRpr(toLit(elimclauses[i]));
        //model[var(x)] = lbool(!sign(x));
	assigns[var(x)] = lbool(!sign(x));
    next:;
    }
}

void Solver::removeClauseForElim(CRef cr)
{
    const Clause& c = ca[cr];

    if (c.learnt())
      for (int i = 0; i < c.size(); i++){
	occurIn.smudge(var(c[i]));
      }
    else
      for (int i = 0; i < c.size(); i++){
	n_occ[toInt(c[i])]--;
	updateElimHeap(var(c[i]));
	occurIn.smudge(var(c[i]));
      }
    if (!removed(cr))
      removeClause(cr);
}

// Returns FALSE if clause is always satisfied ('out_clause' should not be used).
bool Solver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{
    out_clause.clear();
    assert(!_ps.learnt() && !_qs.learnt());

    counter++;
    for (int i = 0; i < _ps.size(); i++) {
      if (var(_ps[i]) != v) {
	if (value(_ps[i]) == l_True)
	  return false;
	else if (value(_ps[i]) != l_False) {
	  seen2[toInt(_ps[i])] = counter;
	  out_clause.push(_ps[i]);
	}
      }
    }
    for (int i = 0; i < _qs.size(); i++){
      if (var(_qs[i]) != v) {
	if (value(_qs[i]) == l_True)
	  return false;
	else if (value(_qs[i]) != l_False) {
	  if (seen2[toInt(~_qs[i])] == counter)
	    return false;
	  else if (seen2[toInt(_qs[i])] != counter)
	    out_clause.push(_qs[i]);
	}
      }
    }
    return true;
}

// Returns FALSE if clause is always satisfied.
bool Solver::merge(const Clause& _ps, const Clause& _qs, Var v, int& size) {
  assert(!_ps.learnt() && !_qs.learnt());
  size=0;
  counter++;
  for (int i = 0; i < _ps.size(); i++) {
    if (var(_ps[i]) != v) {
      if (value(_ps[i]) == l_True)
	return false;
      else if (value(_ps[i]) != l_False) {
	seen2[toInt(_ps[i])] = counter;
	size++;
      }
    }
  }
  for (int i = 0; i < _qs.size(); i++){
    if (var(_qs[i]) != v) {
      if (value(_qs[i]) == l_True)
	return false;
      else if (value(_qs[i]) != l_False) {
	if (seen2[toInt(~_qs[i])] == counter)
	  return false;
	else if (seen2[toInt(_qs[i])] != counter)
	  size++;
      }
    }
  }
  return true;
}

void Solver::storeElimClause(vec<Lit>& elimclauses, Var v, Clause& c)
{
  elimclauses.push(lit_Undef);
  int first = elimclauses.size();
  int v_pos = -1;
  
  // Copy clause to elimclauses-vector. Remember position where the
  // variable 'v' occurs:
  for (int i = 0; i < c.size(); i++){
    if (var(c[i]) == v)
      v_pos = elimclauses.size();
    elimclauses.push(c[i]);
  }
  assert(v_pos != -1);
  
  // Swap the first literal with the 'v' literal, so that the literal
  // containing 'v' will occur first in elimClauses for the clause:
  Lit tmp = elimclauses[v_pos];
  elimclauses[v_pos] = elimclauses[first];
  elimclauses[first] = tmp;
}

bool Solver::cleanClause(CRef cr, int level0Trail) {
  if (removed(cr))
    return false;
  bool sat=false, false_lit=false;
  Clause& c=ca[cr];
  for (int i = 0; i < c.size(); i++){
    if (value(c[i]) == l_True && trailIndex(var(c[i])) < level0Trail){
      sat = true;
      break;
    }
    else if (value(c[i]) == l_False && trailIndex(var(c[i])) < level0Trail){
      false_lit = true;
    }
  }
  if (sat){
    removeClause(cr);
    return false;
  }
  else{
    if (false_lit){
      vec<Lit> myadd_oc;
      if (drup_file) {
	for(int k=0; k<c.size(); k++)
	  myadd_oc.push(c[k]);
      }
      
      int li, lj;
      for (li = lj = 0; li < c.size(); li++){
	if (value(c[li]) != l_False || trailIndex(var(c[li])) >= level0Trail){
	  c[lj++] = c[li];
	}
	else assert(li>1);
      }
      if (lj==2) {
	assert(li>2);
	detachClause(cr, true);
	c.shrink(li - lj);
	attachClause(cr);
      }
      else {
	assert(lj>2);
	c.shrink(li - lj);
      }
      c.calcAbstraction();

      if (drup_file) {
	writeClause2drup('a', c, drup_file);
	writeClause2drup('d', myadd_oc, drup_file);
      }
      
    }
    return true;
  }
}

void Solver::cancelUntilRecord(int record) {
  for (int c = trail.size() - 1; c >= record; c--) {
    Var x = var(trail[c]);
    assigns[x] = l_Undef;
    litTrail[toInt(trail[c])] = record;
  }
  qhead = record;
  trail.shrink(trail.size() - record);
}

void Solver::mySimpleAnalyze(CRef confl, vec<Lit>& out_learnt, bool True_confl)
{
    int pathC = 0;
    Lit p = lit_Undef;
    int index = trail.size() - 1;

    do{
        if (confl != CRef_Undef){
            Clause& c = ca[confl];
            // Special case for binary clauses
            // The first one has to be SAT
            if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {

                assert(value(c[1]) == l_True);
                Lit tmp = c[0];
                c[0] = c[1], c[1] = tmp;
            }
	    
	    //  int nbSeen=0, resolventSize= out_learnt.size()+pathC;
	    
            // if True_confl==true, then choose p begin with the 1th index of c;
            for (int j = (p == lit_Undef && True_confl == false) ? 0 : 1; j < c.size(); j++){
                Lit q = c[j];
		if (trailIndex(var(q)) >= trailRecord) {
		  if (!seen[var(q)])
		  //   nbSeen++;
		  // else
		    {
                    seen[var(q)] = 1;
                    pathC++;
		  }
                }
            }
	    // if (p != lit_Undef && pathC > 1 && nbSeen >= resolventSize) {
	    //   simplereduceClause(confl, pathC);
	    //   //  printf("b* \n");
	    // }
        }
        else if (confl == CRef_Undef){
            out_learnt.push(~p);
        }
        // if not break, while() will come to the index of trail blow 0, and fatal error occur;
        if (pathC == 0) break;
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        // if the reason cr from the 0-level assigned var, we must break avoid move forth further;
        // but attention that maybe seen[x]=1 and never be clear. However makes no matter;
	//	if (trailRecord > index + 1) break;
	assert(trailRecord <= index + 1);
        p = trail[index + 1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC >= 0);
}

// lits stores the simplified clause when it returns false.
bool Solver::propagateClauseAndAnalyze0(CRef cr, Var v, vec<Lit>& propagatedLits) {
  bool True_confl = false;
  CRef confl=CRef_Undef;
  Lit trueLit, vLit=lit_Undef;
  int i;
  Clause& c=ca[cr];
  vec<Lit> lits;
  lits.clear();
  for(int i=0; i<c.size(); i++) {
    if (var(c[i]) == v)
      vLit=c[i];
    else
      lits.push(c[i]);
  }
  assert(vLit != lit_Undef);
  propagatedLits.clear();
  for (i = 0; i < lits.size(); i++){
    if (value(lits[i]) == l_Undef) {
      simpleUncheckEnqueue(~lits[i]);
      confl = simplePropagate();
      if (confl != CRef_Undef)
	break;
      propagatedLits.push(lits[i]);
    }
    else if (value(lits[i]) == l_True){
      assert(reason(var(lits[i])) != CRef_Undef);
      trueLit = lits[i];
      True_confl = true;
      confl = reason(var(trueLit));
      break;
    }
  }
  if (confl != CRef_Undef || True_confl){
    // simp_learnt_clause.clear();
    propagatedLits.clear();
    //   simp_reason_clause.clear();
    if (True_confl)
      propagatedLits.push(trueLit);
    // simpleAnalyze(confl, propagatedLits, simp_reason_clause, True_confl);
    mySimpleAnalyze(confl, propagatedLits, True_confl);
    return false;
  }
  assert(value(vLit) == l_True);
  return true;//all lits have been propagated except vLit that has been forced false
}

// lits stores the simplified clause when it returns false.
bool Solver::propagateClauseAndAnalyze1(CRef cr, Var v, vec<Lit>& propagatedLits, bool& ttlg) {
  bool True_confl = false;
  CRef confl=CRef_Undef;
  Lit trueLit=lit_Undef, vLit=lit_Undef;
  Clause& c=ca[cr];
  propagatedLits.clear(); ttlg=false;
  for(int i=0; i<c.size(); i++) {
    if (var(c[i]) == v)
      vLit=c[i];
    else if (value(c[i]) == l_True) {
      if (reason(var(c[i])) == CRef_Undef) {
	ttlg=true;
	break;
      }
      else if (!True_confl) {
	True_confl = true;
	trueLit = c[i];
	confl=reason(var(trueLit));
      }
    }
    else if (value(c[i]) == l_Undef)
      propagatedLits.push(c[i]);
  }

  if (!ttlg) {  
    assert(vLit != lit_Undef);
    assert(value(vLit) == l_False);
  }

  if (ttlg) {
    return true;
  }
  else if (True_confl) {
    assert(confl != CRef_Undef && trueLit != lit_Undef);
    propagatedLits.clear();
    propagatedLits.push(trueLit);
    mySimpleAnalyze(confl, propagatedLits, True_confl);
    return false;
  }
  else 
    return true;
}

// bool Solver::cancelAndPropagateLit(Lit p) {
//   cancelUntilRecord(trailRecord);
//   if (value(p) == l_Undef) {
//     uncheckedEnqueue(p);
//     if (propagate() != CRef_Undef){
//       ok = false;
//       return false;
//     }
//     trailRecord = trail.size();
//     return true;
//   }
//   return true;
// }

struct clauseSize_lt {
    ClauseAllocator& ca;
    clauseSize_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {

      return ca[x].size() < ca[y].size();
    }
};

struct clauseLBDsize_lt {
    ClauseAllocator& ca;
    clauseLBDsize_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
      return (ca[x].lbd() < ca[y].lbd()) ||
	(ca[x].lbd() == ca[y].lbd() && ca[x].size() < ca[y].size());
    }
};

// if return false and ok is also false, then the instance is unsatisfiable
// if returns false but ok is true, then resolvent is a simplified clause
// if returns true and cr is removed, then cr need not to be considered agin
// if returns true and cr is not removed, then all lits in cr have been propagated.
bool Solver::cancelAndPropagateLitClause(Lit p, CRef cr, Var v, vec<Lit>& resolvent) {
  cancelUntilRecord(trailRecord);
  assert(value(p) == l_Undef);
  uncheckedEnqueue(p);
  if (propagate() != CRef_Undef){
    ok = false;
    return false;
  }
  trailRecord = trail.size();
  resolvent.clear();
  if (cleanClause(cr, trailRecord)) {
    return propagateClauseAndAnalyze0(cr, v, resolvent);
  }
  else
    return true;
}

void Solver:: getWatchedLits(vec<Lit>& resolvent) {
  int j; // the first false lit in resolvent
  if (value(resolvent[0]) != l_False) {
    if (value(resolvent[1]) != l_False)
      return;
    else j=1;
  }
  else if (value(resolvent[1]) != l_False) {
    Lit tmp=resolvent[1];
    resolvent[1] = resolvent[0];
    resolvent[0] = tmp; j=1;
  }
  else j=0;
			  
  for(int i=j+1; i<resolvent.size(); i++) {
    if (value(resolvent[i]) != l_False) {
      Lit tmp=resolvent[i];
      resolvent[i] = resolvent[j];
      resolvent[j] = tmp;
      if (++j > 1)
	return;
    }
  }
}

//#define printResolvent

// Produce clauses in cross product of neg and pos containing v to eliminate v
bool Solver::crossResolvents(vec<CRef>& pos, vec<CRef>& neg, Var v) {
  vec<CRef>& small = pos.size() < neg.size() ? pos : neg;
  vec<CRef>& great = pos.size() < neg.size() ? neg : pos;
  vec<Lit> resolvent1, resolvent2;
  
  if (small.size() == 0)
    return true;
  // if (v==1877)
  //   printf("dsfs ");
  // add_tmp.clear();
  
  sort(small, clauseSize_lt(ca)); sort(great, clauseSize_lt(ca)); 
  assert(subsumptionQueue.size()==0);
  for (int i = 0; i < small.size(); i++) {
    trailRecord=trail.size();
    if (value(v) != l_Undef)
      return true;
    CRef cr=small[i];
    if (!cleanClause(cr, trailRecord))
      continue;
#ifdef printResolvent
    printf("\nc small(%d/%d), with v=%d: ", i, small.size(), v); printClause(ca[cr]);
    printf("-------------------------------------------\n");
#endif
    if (propagateClauseAndAnalyze0(cr, v, resolvent1)) {
      // the lits in cr have been negatively propagated normally
      assert(resolvent1.size() > 0);
      for (int j = 0; j < great.size(); j++) {
	CRef dr = great[j];
	if (cleanClause(dr, trailRecord)) {
#ifdef printResolvent
	  printf("\nc great(%d/%d): ", j, great.size()); printClause(ca[dr]);
#endif
	  bool ttlg;
	  bool res=propagateClauseAndAnalyze1(dr, v, resolvent2, ttlg);
	  if (res) {
	    if (ttlg) {
#ifdef printResolvent
	      printf("c tautology resolvent \n");
#endif    
	      continue;
	    }
	    else {
	      // resolvent2 contains at least two free lits, otherwise
	      // the only free lit would be satisfied
	      assert(resolvent2.size() > 1);
	      for(int aa=0; aa<resolvent1.size(); aa++)
		resolvent2.push(resolvent1[aa]);
#ifdef printResolvent
	      printf("c resolvent from dr and cr: "); printClause(resolvent2);
#endif
	      bool added = addClauseByResolution(resolvent2);
	      assert(added);
	    }
	  }
	  else {
	    //resolvent2 contains the clause obtained from a true conflict of cr and dr
	    // a lit of dr is assigned true when propagating ~cr
	    assert(resolvent2.size() > 1);
#ifdef printResolvent
	    printf("c resolvent from a true conflict of cr and dr: ");
	    printClause(resolvent2);
#endif  
	    bool added = addClauseByResolution(resolvent2);
	    assert(added);
	  }
	}
      }
      cancelUntilRecord(trailRecord);
    }
    else {
      //resolvent1 contains a simplified clause obtained from propagating ~cr
      cancelUntilRecord(trailRecord);
#ifdef printResolvent
      printf("c resolvent from cr: "); printClause(resolvent1);
#endif
      nb1stClauseSimp++; nbSavedResolv += great.size();

      if (!addClauseByResolution(resolvent1))
	return false;
      removeClause(cr);
    }
  }
  trailRecord=trail.size();
  //  cancelUntilRecord(trailRecord);
  // for(int i=0; i<add_tmp.size(); i++)
  //   if (value(add_tmp[i]) == l_Undef) {
  //     //  printf("c ----\n");
  //     uncheckedEnqueue(add_tmp[i]);
  //     if (propagate() != CRef_Undef)
  // 	return false;
  //   }
  //   else assert(value(add_tmp[i])==l_True);
  return true;
}

#define learntLimit 40
//#define printResolventL

// Produce clauses in cross product of neg and pos containing v to eliminate v
bool Solver::crossResolventsL(vec<CRef>& posL, vec<CRef>& negL, Var v) {
  if (value(v) != l_Undef || posL.size() == 0 | negL.size()==0)
    return true;
  //  add_tmp.clear();
  sort(posL, clauseLBDsize_lt(ca)); sort(negL, clauseLBDsize_lt(ca));
  vec<CRef>& small = posL.size() < negL.size() ? posL : negL;
  vec<CRef>& great = posL.size() < negL.size() ? negL : posL;
  vec<Lit> resolvent1, resolvent2;
  int limitS=small.size() < learntLimit ? small.size() : learntLimit;
  int limitG=great.size() < learntLimit ? great.size() : learntLimit;

  // if (v==1877)
  //   printf("dsfs ");
  // assert(subsumptionQueue.size()==0);
  for (int i = 0; i < limitS; i++) {
    trailRecord=trail.size();
    if (value(v) != l_Undef)
      return true;
    CRef cr=small[i];
    if (!cleanClause(cr, trailRecord))
      continue;
#ifdef printResolventL
    printf("\nc small(%d/%d), (%d, %d)), with v=%d: ",
	   i, small.size(), ca[cr].lbd(), ca[cr].size(), v);
    printClause(ca[cr]);
    printf("-------------------------------------------\n");
#endif
    if (propagateClauseAndAnalyze0(cr, v, resolvent1)) {
      // the lits in cr have been negatively propagated normally
      assert(resolvent1.size() > 0);
      for (int j = 0; j < limitG; j++) {
	CRef dr = great[j];
	if (cleanClause(dr, trailRecord)) {
#ifdef printResolventL
	  printf("\nc great(%d/%d), (%d, %d)): ", j, great.size(), ca[dr].lbd(), ca[dr].size());
	  printClause(ca[dr]);
#endif
	  bool ttlg;
	  bool res=propagateClauseAndAnalyze1(dr, v, resolvent2, ttlg);
	  if (res) {
	    if (ttlg) {
#ifdef printResolventL
	      printf("c tautology resolvent \n");
#endif    
	      continue;
	    }
	    else {
	      // resolvent2 contains at least two free lits, otherwise
	      // the only free lit would be satisfied
	      assert(resolvent2.size() > 1);
	      int resLength=resolvent2.size() + resolvent1.size();
	      int sumlbd = ca[dr].lbd() + ca[cr].lbd() - 1;
	      int newlbd = resLength-1 < sumlbd ? resLength-1 : sumlbd;
	      int maxLength = (ca[dr].size() > ca[cr].size()) ? ca[dr].size() : ca[cr].size();
	      if (newlbd <= 6 &&
		  ((resLength <= maxLength) ||
		   (resLength <= clause_limit))) {
		for(int aa=0; aa<resolvent1.size(); aa++)
		  resolvent2.push(resolvent1[aa]);
#ifdef printResolventL
		printf("c resolvent(lbd %d, size %d) from dr and cr: ", newlbd, resolvent2.size());
		printClause(resolvent2);
#endif
		bool added = addClauseByResolution(resolvent2, newlbd);
		assert(added);
	      }
#ifdef printResolventL
	      else printf("c toooo long resolvent (%d, %d+%d) from cr and dr:\n",
			  newlbd, resolvent1.size(), resolvent2.size());
#endif      
	    }
	  }
	  else {
	    //resolvent2 contains the clause obtained from a true conflict of cr and dr
	    // a lit of dr is assigned true when propagating ~cr
	    assert(resolvent2.size() > 1);
	    int newlbd = resolvent2.size()-1 < ca[cr].lbd() ? resolvent2.size()-1 : ca[cr].lbd();
#ifdef printResolventL
	    printf("c resolvent (%d %d) from a true conflict of cr and dr: ",
		   newlbd, resolvent2.size());
	    printClause(resolvent2);
#endif
	    
	    bool added = addClauseByResolution(resolvent2, newlbd);
	    assert(added);
	  }
	}
      }
      cancelUntilRecord(trailRecord);
    }
    else {
      //resolvent1 contains a simplified clause obtained from propagating ~cr
      cancelUntilRecord(trailRecord);
      int newlbd = ca[cr].lbd() < resolvent1.size()-1 ? ca[cr].lbd() : resolvent1.size()-1;
#ifdef printResolventL
      printf("c resolvent (lbd %d, size %d) from cr: ", newlbd, resolvent1.size());
      printClause(resolvent1);
#endif
      nb1stClauseSimpL++; nbSavedResolvL += great.size();
      if (!addClauseByResolution(resolvent1, newlbd))
	return false;
      removeClause(cr);
    }
  }
  trailRecord=trail.size();
  //  cancelUntilRecord(trailRecord);
  // for(int i=0; i<add_tmp.size(); i++)
  //   if (value(add_tmp[i]) == l_Undef) {
  //     //  printf("c ----\n");
  //     uncheckedEnqueue(add_tmp[i]);
  //     if (propagate() != CRef_Undef)
  // 	return false;
  //   }
  //   else assert(value(add_tmp[i])==l_True);
  return true;
}

bool Solver::eliminateVar(Var v, int& savedTrailSize)
 {

    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    // Split the occurrences into positive and negative:
    //
    vec<CRef>& cls = occurIn[v]; //.lookup(v);
    vec<CRef>        pos, neg, posL, negL;
    int nbLearnt=0, totalLits=0;
    pos.clear(); neg.clear();
    // for (int i = 0; i < cls.size(); i++)
    //   if (!ca[cls[i]].learnt() && !removed(cls[i]))
    //     (find(ca[cls[i]], mkLit(v)) ? pos : neg).push(cls[i]);

    int i, j, k;
    for (i = j = 0; i < cls.size(); i++) {
      CRef cr=cls[i];
      if (!removed(cr)) {
	Clause& c=ca[cr];
	Lit p;
	for(k=0; k<c.size(); k++) {
	  if (var(c[k]) == v) {
	    p=c[k];
	    break;
	  }
	}
	if (k<c.size()) {
	  cls[j++] = cr;
	  if (c.learnt()) {
	    nbLearnt++;
	    if (sign(p))
	      negL.push(cr);
	    else posL.push(cr);
	  }
	  else {
	    if (sign(p))
	      neg.push(cr);
	    else pos.push(cr);
	    totalLits += c.size();
	  }
	}
      }
    }
    cls.shrink(i-j);

    // if (nbLearnt>=nbElim)
    //   return true;

    // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
    // clause must exceed the limit on the maximal clause size (if it is set):
    //
    int cnt         = 0;
    int clause_size = 0;
    int limit = pos.size()+neg.size()+grow, resLits=0;

    if (grow<0) {
      for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
	  if (merge(ca[pos[i]], ca[neg[j]], v, clause_size)) {
	    cnt++;
	    resLits += clause_size;
	    if (resLits > totalLits)
	      return true;
	  }
    }
    else 
      for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) && 
                (++cnt > limit || (clause_limit != -1 && clause_size > clause_limit)))
                return true;

    if (cnt>0) {

    //   printf("c eliminating var %d, pos %d, neg %d...\n", v+1, pos.size(), neg.size());

      // int savedClauses=clauses.size(), savedResolvents=resolvents.size();
    int savedTouched=touchedVars.size();
    
    assert(subsumptionQueue.size()==0);

    if (!crossResolvents(pos, neg, v))
      return false;

    if (!crossResolventsL(posL, negL, v))
      return false;

    // reset:
    if (value(v) != l_Undef) {
      for(int i=savedTouched; i<touchedVars.size(); i++)
	touched[touchedVars[i]] = 0;
      touchedVars.shrink(touchedVars.size() - savedTouched);
 //      for(int i=savedResolvents; i<resolvents.size(); i++)
// 	removeClauseForElim(resolvents[i]);
//       resolvents.shrink(resolvents.size() - savedResolvents);
//       subsumptionQueue.clear();
// #ifndef NDEBUG
//       for(int i=savedClauses; i<clauses.size(); i++)
// 	assert(removed(clauses[i]));
// #endif
//       clauses.shrink(clauses.size() - savedClauses);
      if (value(v) == l_True) {
      	for(int i=0; i<pos.size(); i++)
      	  removeClauseForElim(pos[i]);
	for(int i=0; i<posL.size(); i++)
      	  removeClauseForElim(posL[i]);
      }
      else {
      	for(int i=0; i<neg.size(); i++)
      	  removeClauseForElim(neg[i]);
	for(int i=0; i<negL.size(); i++)
      	  removeClauseForElim(negL[i]);
      }
      // return true; // backwardSubsume_(savedTrailSize, false);
          // Free occurs list for this variable:
      // occurIn[v].clear(true);
      //  occurInLocal[v].clear(true);
    
      // // Free watchers lists for this variable, if possible:
      // watches_bin[ mkLit(v)].clear(true);
      // watches_bin[~mkLit(v)].clear(true);
      // watches[ mkLit(v)].clear(true);
      // watches[~mkLit(v)].clear(true);
      
      if (!simplebackwardSubsume_(savedTrailSize, false))
	return false;
      
      if (!simplifyResolvents())
	return false;
    
      //  int savedTrailSize = trail.size();
      return simplebackwardSubsume_(savedTrailSize, false);
    }
    }
        // Delete and store old clauses:
    eliminated[v] = true;
    eliminatedVars.push(v);
    setDecisionVar(v, false);

    if (pos.size() > neg.size()){
      for (int i = 0; i < neg.size(); i++)
	mkElimClause(elimclauses, v, ca[neg[i]]);
      mkElimClause(elimclauses, mkLit(v));
    }else{
      for (int i = 0; i < pos.size(); i++)
	mkElimClause(elimclauses, v, ca[pos[i]]);
      mkElimClause(elimclauses, ~mkLit(v));
    }
    
    for (int i = 0; i < cls.size(); i++)
      removeClauseForElim(cls[i]);
    occurIn.cleanAll();

    nbRemovedClausesByElim += pos.size() + neg.size();

    vec<CRef>& clsLocal = occurInLocal[v];
    for (int i = 0; i < clsLocal.size(); i++)
      if (!removed(clsLocal[i]))
	removeClause(clsLocal[i]);

    // Free occurs list for this variable:
    occurIn[v].clear(true);
    occurInLocal[v].clear(true);
    
    // Free watchers lists for this variable, if possible:
    watches_bin[ mkLit(v)].clear(true);
    watches_bin[~mkLit(v)].clear(true);
    watches[ mkLit(v)].clear(true);
    watches[~mkLit(v)].clear(true);

    if (!simplebackwardSubsume_(savedTrailSize, false))
      return false;

    if (!simplifyResolvents())
      return false;
    
    //  int savedTrailSize = trail.size();
    return simplebackwardSubsume_(savedTrailSize, false);
}

#define simplifyTicksLimit 1000000000

bool Solver::eliminate_() {
  int trail_size_last = trail.size();
  uint64_t saved_s_ticks = s_ticks;

  // Main simplification loop:
  while(!elim_heap.empty() || trail_size_last < trail.size()) {
    if (!simplebackwardSubsume_(trail_size_last, false))
      return false;
    
    for (int cnt = 0; !elim_heap.empty(); cnt++){
      Var elim = elim_heap.removeMin();
      
      if (isEliminated(elim) || value(elim) != l_Undef) continue;
      
      // At this point, the variable may have been set by assymetric branching, so check it
      // again. Also, don't eliminate frozen variables:
      if (value(elim) == l_Undef && !eliminateVar(elim, trail_size_last)){
	ok = false; goto cleanup; }
      
      checkGarbageForElimVars();
      if (s_ticks - saved_s_ticks > simplifyTicksLimit)
	elim_heap.clear();
    }
  }
  
  gatherTouchedClauses();
  if (!simplebackwardSubsume_(trail_size_last))
    return false;
  
 cleanup:
  // To get an accurate number of clauses.
  if (trail_size_last != trail.size()) {
    removeSatisfied(learnts_core); // Should clean core first.
    safeRemoveSatisfied(learnts_tier2, TIER2);
    safeRemoveSatisfied(learnts_local, LOCAL);
    safeRemoveSatisfied(auxiLearnts, LOCAL);
    removeSatisfied(clauses);
  }
  else{
    purgeClauses(learnts_core);
    purgeClauses(learnts_tier2);
    purgeClauses(learnts_local);
    purgeClauses(auxiLearnts);
    purgeClauses(clauses);
    // int i,j;
    // for (i = j = 0; i < clauses.size(); i++)
    //   if (!removed(clauses[i]))
    // 	//  if (ca[clauses[i]].mark() == 0)
    // 	clauses[j++] = clauses[i];
    // clauses.shrink(i - j);
  }
  
  checkGarbageForElimVars();
#ifndef NDEBUG
  if (elimclauses.size() > 0)
    printf("c |  Eliminated clauses:     %10.2f Mb  grow %d                                    |\n", 
	   double(elimclauses.size() * sizeof(uint32_t)) / (1024*1024), grow);
#endif
  return ok;
}

void Solver::collectOriginalClauses(vec<CRef>& clauseSet) {
  int i, j;
  for(i=0, j=0; i<clauseSet.size(); i++)
    if (cleanClause(clauseSet[i])) {
      CRef cr = clauseSet[i];
      Clause& c=ca[cr];
      for(int k=0; k<c.size(); k++) {
	occurIn[var(c[k])].push(cr);
	n_occ[toInt(c[k])]++;
      }
      clauseSet[j++] = cr;
      // subsumptionQueue.insert(cr);
      //    subsumptionQueue.push(cr);
    }
  clauseSet.shrink(i-j);
}

void Solver::buildElimHeap() {
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
      if (value(v) == l_Undef && (!isEliminated(v)) &&
	  (n_occ[toInt(mkLit(v))] > 0 || n_occ[toInt(~mkLit(v))] > 0))
	vs.push(v);
    elim_heap.build(vs);
#ifndef NDEBUG
    printf("c %d vars to eliminate\n", vs.size());
#endif
}

void Solver::collectLocalClauses(vec<CRef>& clauseSet) {
  int i, j;

  for(i=0, j=0; i<clauseSet.size(); i++) {
    CRef cr = clauseSet[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    assert(c.learnt());
    if (c.mark() != LOCAL)
      continue;
    if (cleanClause(cr)) {
      for(int k=0; k<c.size(); k++) {
	occurInLocal[var(c[k])].push(cr);
      }
      clauseSet[j++] = cr;
    }
  }
  clauseSet.shrink(i-j);
}

// void Solver::collectLocalClauses(vec<CRef>& clauseSet) {
//   int i, j;
//   for(i=0, j=0; i<clauseSet.size(); i++) {
//     CRef cr=clauseSet[i];
//     Clause& c=ca[cr];
//     assert(c.learnt());
//     if (!removed(cr) && c.mark() == LOCAL) {
//       for(int k=0; k<c.size(); k++)
// 	occurInLocal[var(c[k])].push(cr);
//       clauseSet[j++] = cr;
//     }
//   }
//   clauseSet.shrink(i-j);
// }

// void Solver::eliminateLearntClausesContainingElimVar(vec<CRef>& learnts) {
//   int i, j, k;
//   //  int cnt=0;
//   for(i=0, j=0; i<learnts.size(); i++) {
//     CRef cr=learnts[i];
//     Clause& c=ca[cr];
//     if (!removed(cr)) {
//       for(k=0; k<c.size(); k++)
// 	if (isEliminated(var(c[k])))
// 	  break;
//       if (k < c.size())
// 	removeClause(cr);
//       else
// 	learnts[j++] = cr;
//     }
//     //  else printf("removed %d\n", ++cnt);
//   }
//   learnts.shrink(i-j);
// }

bool Solver::eliminate() {
  //  bool res = true;
  //  int iter = 0;
  //  int n_cls, n_cls_init, n_vars;

  nbUnitViviResolv=0, shortened = 0, nbSimplifing = 0, nbRemovedLits=0;
  saved_s_up = s_propagations;
  
#ifndef NDEBUG
  double elimTime = cpuTime();
#endif
  
  uint64_t saved_s_ticks = s_ticks;
  

  if (!backwardSubsume())
    return false;
  
  if (equivLits.size() > prevEquivLitsNb) {
    // collectClauses(learnts_local, LOCAL);
    // collectClauses(auxiLearnts, LOCAL);
    collectLocalClauses(learnts_local);
    collectLocalClauses(auxiLearnts);
    if (!eliminateEqLits_(prevEquivLitsNb))
      return false;
  }

  for(int i=0; i<nVars(); i++) {
    occurIn[i].clear(); occurInLocal[i].clear();
    n_occ[toInt(mkLit(i))] = 0; n_occ[toInt(~mkLit(i))] = 0;
  }
  collectClauses(clauses);
  if (clauses.size() > 1000000)
    subsumptionQueue.clear();
  collectClauses(learnts_core, CORE);
  collectClauses(learnts_tier2, TIER2);

  subsumptionQueue.clear(); resolvents.clear(); nbAllResolvs=0;
    // occurIn.init(nVars());
    // for(int i=0; i<nVars(); i++) {
    //   occurIn[i].clear();
    //   n_occ[toInt(mkLit(i))] = 0; n_occ[toInt(~mkLit(i))] = 0;
    // }

    // collectOriginalClauses(clauses);
  collectLocalClauses(learnts_local);
  collectLocalClauses(auxiLearnts);

  // if (!backwardSubsume())
  //   return false;

  // collectLocalClauses(learnts_local);
  // collectLocalClauses(auxiLearnts);
  
  // if (equivLits.size() > prevEquivLitsNb) {
  //   subsumptionQueue.clear();
  //   if (!eliminateEqLits_(prevEquivLitsNb))
  //     return false;
  // }
    
  //   subsumptionQueue.clear();
  //   occurIn.init(nVars()); occurInLocal.init(nVars());
  //   for(int i=0; i<nVars(); i++) {
  //     occurIn[i].clear();  occurInLocal[i].clear();
  //   }

  //   collectClauses(clauses);
  //   subsumptionQueue.clear();
    
  //   collectClauses(learnts_core, CORE);
  //   collectClauses(learnts_tier2, TIER2);
  //   collectClauses(learnts_local, LOCAL);
  //   collectClauses(auxiLearnts, LOCAL);
  //   subsumptionQueue.clear();
    
  //   if (!eliminateEqLits_(prevEquivLitsNb))
  //     return false;
  // }

    // if (!backwardSubsume() )
    //   return false;

    subsumptionQueue.clear(); resolvents.clear(); nbAllResolvs=0;
    // occurIn.init(nVars());
    // for(int i=0; i<nVars(); i++) {
    //   occurIn[i].clear();
    //   n_occ[toInt(mkLit(i))] = 0; n_occ[toInt(~mkLit(i))] = 0;
    // }

    // collectOriginalClauses(clauses);
    
    // collectLocalClauses(learnts_local);
    // collectLocalClauses(auxiLearnts);

#ifndef NDEBUG
    printf("c before variable elimination....\n"); 
    printf("c original clauses %d, learnts_core %d, learnts_tier2 %d, learnts_local %d, auxiLearnts %d, trail %d\n",
	   clauses.size(), learnts_core.size(), learnts_tier2.size(), learnts_local.size(), auxiLearnts.size(), trail.size());
#endif
    
    for(grow = -2; grow<4 && s_ticks - saved_s_ticks <= simplifyTicksLimit; grow+=2) {
      int savednbRemovedClausesByElim=nbRemovedClausesByElim,
	savedEliminatedVars=eliminatedVars.size(), savednbAllResolvs=nbAllResolvs,
	savednbSavedResolv=nbSavedResolv, savednb1stClauseSimp=nb1stClauseSimp,
	savednbLearntResolvs=nbLearntResolvs, savednb1stClauseSimpL=nb1stClauseSimpL, savednbSavedResolvL=nbSavedResolvL;
      int  savedsbsmRslv=sbsmRslv, saveddelLitRslv=delLitRslv;
      uint64_t savedUp=s_propagations;
    buildElimHeap();
    if (!eliminate_())
      return false;

#ifndef NDEBUG
    printf("c %d(%d) vars eliminated, %d(%d) clauses removed, %d(%d) resolvs added, nbLnResolvs %d(%d)\n",
	   eliminatedVars.size()-savedEliminatedVars, eliminatedVars.size(),
	   nbRemovedClausesByElim - savednbRemovedClausesByElim,
	   nbRemovedClausesByElim, nbAllResolvs-savednbAllResolvs, nbAllResolvs, nbLearntResolvs-savednbLearntResolvs, nbLearntResolvs);
    printf("c %d(%d) nb1stClauseSimpL, %d(%d) nbSavedResolvL\n",
	   nb1stClauseSimpL-savednb1stClauseSimpL, nb1stClauseSimpL,
	   nbSavedResolvL-savednbSavedResolvL, nbSavedResolvL);
    printf("c %d(%d) 1stClauseSimp, %d(%d) nbSavedResolv, s_up %llu, s_ticks %llu\n",
	   nb1stClauseSimp-savednb1stClauseSimp, nb1stClauseSimp,
	   nbSavedResolv-savednbSavedResolv, nbSavedResolv, s_propagations-savedUp, s_ticks-saved_s_ticks);
    printf("c sbsmRslv %d(%d), delLitRslv %d(%d)\n",
	   sbsmRslv-savedsbsmRslv, sbsmRslv, delLitRslv-saveddelLitRslv, delLitRslv);
#endif
    }
    assert(subsumptionQueue.size() == 0);
    
    // int trail_size_last = trail.size();
    // if (!simplifyResolvents())
    //   return false;

    // if (!backwardSubsume_(trail_size_last))
    //   return false;
    
    //    eliminateLearntClausesContainingElimVar(learnts_local);
    //    eliminateLearntClausesContainingElimVar(auxiLearnts);

    for(int i=0; i<nVars(); i++) {
      occurIn[i].clear(); occurInLocal[i].clear();
    }
    subsumptionQueue.clear();
    
    checkGarbage();

#ifndef NDEBUG
    printf("c after variable elimination....\n"); 
    printf("c original clauses %d, learnts_core %d, learnts_tier2 %d, learnts_local %d, auxiLearnts %d, trail %d\n\n",
	   clauses.size(), learnts_core.size(), learnts_tier2.size(), learnts_local.size(), auxiLearnts.size(), trail.size());

    //#ifndef NDEBUG
    double avgRemovedLits = shortened > 0 ? (double)nbRemovedLits/shortened : 0;
    printf("c resolvents %d, nbSimplifing: %d, nbShortened: %d\n",
	   nbAllResolvs, nbSimplifing, shortened);
    printf("c avgRemovedLits %4.3lf, nbUnits %d, s_up %llu, elimTime %5.2lfs, s_ticks %llu\n",
	   avgRemovedLits, nbUnitViviResolv, s_propagations-saved_s_up, cpuTime() - elimTime,  s_ticks-saved_s_ticks);
    totalelimTime += cpuTime() - elimTime;
#endif
    
    //#endif
    return true;
}

bool Solver::isSubsumed(CRef dr) {
  Clause& d=ca[dr];
  counter++;
  for (int i = 0; i < d.size(); i++) {
    seen2[toInt(d[i])]=counter;
  }
  for(int i=0; i<subsumptionQueue.size(); i++) {
    CRef cr=subsumptionQueue[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    if ((c.size() > d.size()) || ((c.abstraction() & (~d.abstraction())) !=0))
      continue;
    Lit ret = lit_Undef;
    for(int k=0; k<c.size(); k++) {
      // if (seen2[toInt(~c[k])] == counter) {
      // 	if (ret == lit_Undef)
      // 	  ret = c[k];
      // 	else {
      // 	  // sbsmTtlg++;
      // 	  ret = lit_Error;
      // 	  break;
      // 	}
      // }
      // else
      if (seen2[toInt(c[k])] != counter) {
	ret = lit_Error;
	break;
      }
    }
    if (ret == lit_Undef) {
      if (!d.learnt() && c.learnt()) {
	if (d.size() > c.size()) {
	  if (drup_file)
	    writeClause2drup('d', d, drup_file);
	  detachClause(dr, true);
	  for(int k=0; k<c.size(); k++)
	    d[k]=c[k];
	  d.shrink(d.size() - c.size());
	  attachClause(dr);
	  if (drup_file)
	    writeClause2drup('a', d, drup_file);
	}
	removeClause(cr);  removeClauseFromOccur(cr, true);
	subsumptionQueue[i] = dr;
      }
      else {
	removeClause(dr);  removeClauseFromOccur(dr, true);
      }
      sbsmRslv++;
      return true;
    }
    // else if (ret != lit_Error) {
    //   delLitRslv++;
    //   if (d.size() == 2){
    // 	removeClause(dr);  removeClauseFromOccur(dr);
    // 	d.strengthen(~ret);
    //   }
    //   else {
    // 	detachClause(dr, true);
    // 	d.strengthen(~ret);
    // 	attachClause(cr);
    // 	remove(occurIn[var(ret)], cr);
    //   }
    // }
  }
  return false;
}

#define simplifyUPlimit 200000000

bool Solver::simplifyResolvents() {
  //  static int nb=0;
  int ci; //shortened = 0, nbSimplifing = 0, nbRemovedLits=0, nbUnits=0;
  // uint64_t saved_s_up = s_propagations;
  vec<Lit> lits, myadd_occ;
  assert(decisionLevel() == 0);
  sort(resolvents, clauseSize_lt(ca));
  for (ci = 0; ci < resolvents.size() && (starts > 0 || s_propagations - saved_s_up <= simplifyUPlimit); ci++){
    CRef cr = resolvents[ci];
    Clause& c = ca[cr];
    int savedSize=c.size();
    if (starts>0) {
      lits.clear();
      for(int i=0; i<c.size(); i++)
	lits.push(c[i]);
    }
    if (cleanClause(cr)) {
      if (c.size() == 2 &&
	  (litTrail[toInt(~c[0])] >= trail.size() && litTrail[toInt(~c[1])] >= trail.size())) {
	if (starts>0 && c.size() < savedSize) {
	  counter++;
	  for(int i=0; i<c.size(); i++)
	    seen2[var(c[i])] = counter;
	  for(int i=0; i<lits.size(); i++)
	    if (seen2[var(lits[i])] != counter) {
	      remove(occurIn[var(lits[i])], cr);
	      n_occ[toInt(lits[i])]--;
	      updateElimHeap(var(lits[i]));
	    }
	}
	continue;
      }
      if (starts>0 && isSubsumed(cr))
	continue;
      int saved_size=c.size();
      
      if (drup_file){
	myadd_occ.clear();
	for (int i = 0; i < c.size(); i++) myadd_occ.push(c[i]);
      }
      
      nbSimplifing++;
      
      int beforeSize = c.size();
      assert(c.size() > 1);
      detachClause(cr, true);
      // simplify a learnt clause c
      simplifyLearnt(c);
      assert(c.size() > 0);
      int afterSize = c.size();
      
      if(drup_file && saved_size !=c.size()){
	writeClause2drup('a', c, drup_file);
	writeClause2drup('d', myadd_occ, drup_file);
// #ifdef BIN_DRUP
// 	binDRUP('a', c , drup_file);
// 	binDRUP('d', add_oc, drup_file);
// #else
// 	for (int i = 0; i < c.size(); i++)
// 	  fprintf(drup_file, "%i ", (repr[var(c[i])] + 1) * (-2 * sign(c[i]) + 1));
// 	fprintf(drup_file, "0\n");
	
// 	fprintf(drup_file, "d ");
// 	for (int i = 0; i < add_oc.size(); i++)
// 	  fprintf(drup_file, "%i ", (repr[var(add_oc[i])] + 1) * (-2 * sign(add_oc[i]) + 1));
// 	fprintf(drup_file, "0\n");
// #endif
      }
      //printf("beforeSize: %2d, afterSize: %2d\n", beforeSize, afterSize);
      if (c.size() == 1){
	for(int i=0; i<lits.size(); i++)
	  remove(occurIn[var(lits[i])], cr);
	  // when unit clause occur, enqueue and propagate
	nbUnitViviResolv++;
	uncheckedEnqueue(c[0]);
	// delete the clause memory in logic
	c.mark(1);
	ca.free(cr);
	if (propagate() != CRef_Undef){
	  ok = false;
	  return false;
	}

	//#ifdef BIN_DRUP
	//                    binDRUP('d', c, drup_file);
	//#else
	//                    fprintf(drup_file, "d ");
	//                    for (int i = 0; i < c.size(); i++)
	//                        fprintf(drup_file, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
	//                    fprintf(drup_file, "0\n");
	//#endif
      }
      else{
	if (afterSize < beforeSize) {
	  shortened++; nbRemovedLits += beforeSize - afterSize;
	}
	if (afterSize < savedSize) {
	  c.calcAbstraction(); subsumptionQueue.push(cr);
	  if (starts>0) {
	    counter++;
	    for(int i=0; i<c.size(); i++)
	      seen2[var(c[i])] = counter;
	    for(int i=0; i<lits.size(); i++)
	      if (seen2[var(lits[i])] != counter) {
		remove(occurIn[var(lits[i])], cr);
		n_occ[toInt(lits[i])]--;
		updateElimHeap(var(lits[i]));
	      }
	  }
	}
	attachClause(cr);
      }
    }
  }
// #ifndef NDEBUG
//   double avgRemovedLits = shortened > 0 ? (double)nbRemovedLits/shortened : 0;
//   printf("c resolvents %d, nbSimplifing: %d, nbShortened: %d\n",
// 	 resolvents.size(), nbSimplifing, shortened);
//   printf("c avgRemovedLits %4.3lf, nbUnits %d, s_up %llu\n",
// 	 avgRemovedLits, nbUnits, s_propagations-saved_s_up);
// #endif
  resolvents.clear();
  return true;
}

void Solver::checkGarbageForElimVars() {
  if (ca.wasted() > ca.size() * garbage_frac) {
    
    // ClauseAllocator to(ca.size() - ca.wasted());
    ClauseAllocator to(ca.wasted() > ca.size()/2 ? ca.size()/2 : ca.size() - ca.wasted()); 
    relocAll(to);
    occurIn.cleanAll();
    int i, j;
    for(i=0; i<nVars(); i++) {
      vec<CRef>& cls=occurIn[i];
      for(j=0; j<cls.size(); j++)
	ca.reloc(cls[j], to);
      
      vec<CRef>& clsLocal=occurInLocal[i];
      for(j=0; j<clsLocal.size(); j++)
	ca.reloc(clsLocal[j], to);
    }
    for(i=j=0; i<subsumptionQueue.size(); i++)
      if (!removed(subsumptionQueue[i])) {
	ca.reloc(subsumptionQueue[i], to);
	subsumptionQueue[j++]=subsumptionQueue[i];
      }
    subsumptionQueue.shrink(i-j);
    
    for(i=j=0; i<resolvents.size(); i++) {
      if (!removed(resolvents[i])) {
	ca.reloc(resolvents[i], to);
	resolvents[j++] = resolvents[i];
      }
    }
    resolvents.shrink(i-j);
    
    to.moveTo(ca);
  }
}

bool Solver::simplesubsumeClauses(CRef cr, int& subsumed, int& deleted_literals) {
  Clause& c  = ca[cr];
  assert(c.size() > 1 || value(c[0]) == l_True);// Unit-clauses should have been propagated before this point.
  // Find best variable to scan:
  Var best = var(c[0]);
  for (int i = 1; i < c.size(); i++)
    if (occurIn[var(c[i])].size() < occurIn[best].size())
      best = var(c[i]);
  
  // Search all candidates:
  vec<CRef>& _cs = occurIn.lookup(best);
  CRef*       cs = (CRef*)_cs;
  for (int j = 0; j < _cs.size(); j++) {
    assert(!removed(cr));
    CRef dr=cs[j];
    if (dr != cr && !removed(dr)){
      Clause& d=ca[dr];
      // Lit l1 = c.subsumes(d);
      Lit l = simplesubsume(c, d);
      // assert(l==l1);
      if (l == lit_Undef) {
	if (c.learnt() && !d.learnt()) {
	  if (c.size() < d.size()) {
	    if (drup_file)
	      writeClause2drup('d', d, drup_file);
	    detachClause(dr, true); removeClauseFromOccur(dr, true);
	    for(int k=0; k<c.size(); k++) {
	      d[k] = c[k];
	      vec<CRef>& cls=occurIn[var(d[k])];
	      int m;
	      for(m=0; m<cls.size(); m++)
		if (cls[m] == cr) {
		  cls[m]=dr; break;
		}
	      assert(m<cls.size());
	    }
	    d.shrink(d.size() - c.size());
	    d.setAbs(c.abstraction());
	    d.setSimplified(c.simplified());
	    d.set_lbd(c.lbd());
	    attachClause(dr);
	    if (drup_file)
	      writeClause2drup('a', d, drup_file);
	  }
	  else removeClauseFromOccur(cr);
	  subsumed++; removeClause(cr); subsumptionQueue.push(dr); 
	  return true;
	}
	else {
	  subsumed++, removeClause(dr); removeClauseFromOccur(dr);
	}
	// if (c.learnt() && !d.learnt()) {
	//   c.promote();
	//   clauses.push(cr);
	// }
	// subsumed++, removeClause(dr); removeClauseFromOccur(dr);
      }
      else if (l != lit_Error){
	deleted_literals++;
	if (!simpleStrengthenClause(dr, ~l))
	  return false;
	// Did current candidate get deleted from cs? Then check candidate at index j again:
	if (var(l) == best)
	  j--;
      }
    }
  }
  return true;
}

// struct clauseSize_lt {
//     ClauseAllocator& ca;
//     clauseSize_lt(ClauseAllocator& ca_) : ca(ca_) {}
//     bool operator () (CRef x, CRef y) {

//       return ca[x].size() < ca[y].size();
//     }
// };

#define sbsmLimit 5000000

bool Solver::simplebackwardSubsume_(int& savedTrailSize, bool verbose) {
  //  int savedTrail=trail.size();
  int mySavedTrail=trail.size();
  //int savedOriginal;
  // int cnt = 0;
  int subsumed = 0, deleted_literals = 0, nbSubsumes=0;

  int mysbsmLimit=sbsmLimit;
  sbsmTtlg=0; sbsmAbsFail=0; allsbsm=0;

#ifndef NDEBUG
  double sbsmTime;
  if (verbose)
    sbsmTime = cpuTime();
#endif

  sort(subsumptionQueue, clauseSize_lt(ca));
  // savedOriginal = clauses.size();
  assert(decisionLevel() == 0);
  int initQueueSize=subsumptionQueue.size();
  while (subsumptionQueue.size() > 0 || savedTrailSize < trail.size()) {
    // Check top-level assignments by creating a dummy clause and placing it in the queue:
    if (subsumptionQueue.size() == 0 && savedTrailSize < trail.size()){
      Lit l = trail[savedTrailSize++];
      ca[bwdsub_tmpunit][0] = l;
      ca[bwdsub_tmpunit].calcAbstraction();
      //subsumptionQueue.insert(bwdsub_tmpunit);
      subsumptionQueue.push(bwdsub_tmpunit);
      if (allsbsm > mysbsmLimit)
	mysbsmLimit += sbsmLimit;
    }

    //  int initQueueSize=subsumptionQueue.size();
    for(int i=0; i<subsumptionQueue.size(); i++) {
      CRef    cr = subsumptionQueue[i]; //subsumptionQueue.peek(); subsumptionQueue.pop();
      if (removed(cr)) continue;
      nbSubsumes++;
      if (!simplesubsumeClauses(cr, subsumed, deleted_literals)) {
	printf("c a conflict is found during backwardSubsumptionCheck\n");
	occurIn.cleanAll();
	return false;
      }
      if (sbsmAbsFail > mysbsmLimit)
      	subsumptionQueue.clear();
      else
	if (i==initQueueSize) {
	// printf("c initQueue %d, %d subsumed, %d deleted literals, %d fixed vars\n", initQueueSize, subsumed, deleted_literals, trail.size() - mySavedTrail);
	//	mySavedTrail=trail.size();
	initQueueSize=subsumptionQueue.size();
	//	printf("c subsumption queue grows to %d\n", initQueueSize);
	int j, k;
	for(j=0, k=i+1; k<subsumptionQueue.size(); k++)
	  subsumptionQueue[j++] = subsumptionQueue[k];
	subsumptionQueue.shrink(k-j);
	sort(subsumptionQueue, clauseSize_lt(ca));
	//	printf("\n");
	i=-1;
	continue;
      }
    }
    subsumptionQueue.clear();
  }
#ifndef NDEBUG
  if (verbose) {
    printf("c %d subsumptions, %d subsumed, %d delLits, %d(%d) fixedVars\n", nbSubsumes, subsumed, deleted_literals, trail.size() - mySavedTrail, trail.size());
    float rate1, rate2;
    if (allsbsm==0) {
      rate1=0; rate2=0;
    }
    else {
      rate1=(float)(sbsmTtlg)/(allsbsm);
      rate2=(float)(sbsmAbsFail)/(allsbsm);
    }
  printf("c allsbsm %d, sbsmTtlg %d (%5.4f), sbsmAbsFail %d(%5.4f)\n",
	 allsbsm, sbsmTtlg, rate1, sbsmAbsFail, rate2);
  }
  //#ifndef NDEBUG
  if (verbose) {
    double thissbsmtime = cpuTime()-sbsmTime;
    printf("c sbsmTime %5.2lfs\n",  thissbsmtime);
    totalsbsmTime += thissbsmtime;
  }
#endif
  
  occurIn.cleanAll();
  return true;
}

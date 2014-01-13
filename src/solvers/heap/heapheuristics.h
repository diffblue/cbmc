/*
** heapheuristics.h
**
**
*/
#include "heaprefine.h"
#ifndef HEAPHEURISTICS
#define HEAPHEURISTICS

class heapheuristics {
 public:

  upwardCompleteness::s interpolate(heapabs& sol, heaptrans& trans) {
    std::vector< meetIrreduciblep > v; 
    clauset* learntClause;

    debugc("Interpolate", 1);
    //assert(sol.trail.size() > 0);

    // gather all the decisions leading to the current conflict
    for (trailt::const_iterator it = sol.trail.begin(); it != sol.trail.end(); ++it) {
      if ((*it)->reason == this) {
    	meetIrreduciblep mi = (*it)->inference;
    	mi->complement();
    	v.push_back(mi);
      }
    }

    // complement the gathered decisions
    if (v.size() > 0) {
      learntClause = trans.create_disjunction(v);
      debugc("##################################################################", 1);
      debugc("[interpolate]: Learned clause: " << *learntClause, 1);
      debugc("##################################################################", 1);

      trans.insert_clause(learntClause);
      trans.original_formula = trans.formula;
      debugc("[interpolate]: formula after interpolation = " << trans.formula, 1); 
      return upwardCompleteness::Complete;
    }
    // there were no decisions taken
    return upwardCompleteness::Top;
  }

  hintt get_next_hint(heapabs& abs, heaptrans& trans, downwardCompleteness::s complete) {
    hintt hint;
    bool firsthint = false;
    bool candidate_hint;

    debugc("[get_next_hint] : hints = " << trans.hint, 1);

    // propositional incompleteness or imprecise transformer?
    hintPriority::s hintp = (complete == downwardCompleteness::IncompleteProp) ? hintPriority::High : hintPriority::Low;

    debugc("[get_next_hint]", 0);

    int max_priority = 0;
    for(hintst::iterator it = trans.hint.begin(); it != trans.hint.end() /*&& !candidate_hint*/; ++it) {
      solutiont new_hint;
      
      debugc("[get_next_hint] : hint = " << it->first, 0);
      candidate_hint = false;
      
      if(it->second > max_priority || !firsthint) {
	// some preceding decision might have rendered the hint or some of its conjuncts obsolete
	for(solutiont::iterator it1 = (it->first).begin(); it1 != (it->first).end(); ++it1) {
	  debugc("[get_next_hint] : hint conjunct = " << *it1, 1);
	
	  entailResult::s ret1 = abs.entails(*it1);

	  if (ret1 == entailResult::Incomplete) {
	    // candidate hints
	    new_hint.insert(*it1);
	    candidate_hint = true;
	    debugc("[get_next_hint] : candidate = " << *it1, 1);
	    debugc("[get_next_hint] : tmp hint = " << new_hint, 1);
	  }

	}

	if (candidate_hint && !firsthint) {
	  // a possible hint if case all the priorities are 0
	  max_priority = it->second;
	  hint = std::make_pair(new_hint, it->second);
	  firsthint = true;
	}
	
	// the desired priority?
	if (candidate_hint && /*it->second == hintp*/ it->second > max_priority) {
	  max_priority = it->second;
	  hint = std::make_pair(new_hint, it->second);
	  debugc("[get_next_hint] : (1) found hint with higher priority " << hint, 1);
	  //return hint;
	}
      }
    }
    
    assert(firsthint == true);

    // no other option but returning a different priority hint
    debugc("[get_next_hint] : (2) hint = " << hint, 1);
    return hint;
  }

  int extrapolate (heapabs& sol, heaptrans& trans, downwardCompleteness::s complete) {
    hintt decision;

    debugc("Extrapolate", 1);
    assert (trans.hint.size() > 0);

    debugc("[extrapolate]: hint before extrapolation = " << trans.hint, 0);

    decision = get_next_hint(sol, trans, complete);

    debugc("[extrapolate]: hint after extrapolation = " << trans.hint, 0);

    debugc("[extrapolate]: decision = " << decision.first << " and existent solution = " << sol, 0);

    formulat decision_f;

    // checking
    for(solutiont::iterator it = (decision.first).begin(); it!= (decision.first).end(); ++it) {
        clauset* newclause = new std::vector<heaplitp>();
	newclause->push_back((*it)->lit);
	decision_f.push_back(newclause);
    }

    entailResult::s res = sol.entails(&decision_f);
    assert( res == entailResult::Incomplete); 

    // adding the decision to the solution
    for(solutiont::iterator it = (decision.first).begin(); it!= (decision.first).end(); ++it) {
	sol.add_lit(*it);
	debugc("[extrapolate] : added to the solution : " << *it, 1);
	//inferenceRecord* ir = new inferenceRecord(*it, this);
	//sol.trail.insert(ir);
    }

    inferenceRecord* ir = new inferenceRecord(*(decision.first.begin()), this);
    sol.trail.insert(ir);


    debugc("##################################################################", 1);
    debugc("[extrapolate]: Decision: " << decision_f, 1);
    debugc("##################################################################", 1);
    //sol.add_lit(decision.first);
    //inferenceRecord* ir = new inferenceRecord(decision.first, this);
    //sol.trail.insert(ir);

    trans.hint.erase(decision);
    return 1;
    }

};

#endif

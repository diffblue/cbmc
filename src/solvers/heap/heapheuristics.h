/*
** heapheuristics.h
**
**
*/
#ifndef HEAPHEURISTICS
#define HEAPHEURISTICS

#include "heaprefine.h"

class heapheuristics {
 public:

  upwardCompleteness::s interpolate(heapabs& sol, heaptrans& trans) {
    std::vector< meetIrreduciblep > v; 
    clauset* learntClause;

    debug("Interpolate");
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
      debug("##################################################################");
      debug("[interpolate]: clause to learn: " << *learntClause);
      debug("##################################################################");
      trans.insert_clause(learntClause);
      debug("[interpolate]: formula after interpolation = " << trans.formula); 
      return upwardCompleteness::Complete;
    }
    // there were no decisions taken
    return upwardCompleteness::Top;
  }

  meetIrreduciblep get_next_hint(heapabs& abs, heaptrans& trans) const {
    meetIrreduciblep hint;

    debugc("[get_next_hint]", 0);

    for(hintt::const_iterator it = trans.hint.begin(); it != trans.hint.end(); ++it) {
      entailResult::s ret1 = abs.entails(it->first);

      ((it->first)->lit)->complement();
      // check that the formula does not already contain the negation of the literal 
      bool ret2 = trans.formula_contains_literal((it->first)->lit, abs);
      ((it->first)->lit)->complement();
      if (ret1 == entailResult::Incomplete && !ret2) {
	// it's a possible hint
	hint = it->first;
	debugc("[get_next_hint] : valid hint = " << hint, 1);

	if (it->second == hintPriority::High)
	  // it's also high priority
	  return hint;
      }
    }
    
    debugc("[get_next_hint] : hint = " << hint, 1);

    // no other option but returning a low priority hint
    return hint;
  }

  // todo: extrapolate depends on the trans as well as i'm getting a hint 
  // that has not already been considered... can fix this by removing any 
  // used hint and making sure it's not added again
  int extrapolate (heapabs& sol, heaptrans& trans) {
    meetIrreduciblep decision;

    debug("Extrapolate");
    debugc("[extrapolate]: sol.contents = " << sol.contents, 0);
    assert (trans.hint.size() != 0);

    debugc("[extrapolate]: hint before extrapolation = " << trans.hint, 1);
    //decision = sol.hint[sol.hint.size()-1];
    //decision = *(sol.hint.begin());
    assert(trans.hint.size()>0);
    decision = get_next_hint(sol, trans);
    assert(decision != NULL);
    //sol.hint.erase(decision);
    debugc("[extrapolate]: hint after extrapolation = " << trans.hint, 0);

    debugc("[extrapolate]: decision = " << decision << " and existent solution = " << sol, 1);
    assert(sol.entails(decision) == entailResult::Incomplete); 

    debug("##################################################################");
    debug("Decision: " << decision);
    debug("##################################################################");
    sol.add_lit(decision);
    inferenceRecord* ir = new inferenceRecord(decision, this);
    //sol.trail.push_back(ir);
    sol.trail.insert(ir);
    return 1;
    }

};

#endif

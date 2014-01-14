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
      //debugc("[interpolate] : literal_table before interpolation = " << trans.literal_table, 1);
      trans.add_to_literal_table(learntClause);
      // backup
      trans.original_formula = trans.formula;
      trans.original_literal_table = trans.literal_table;
      trans.original_unit_clauses = trans.unit_clauses;
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

    if(hintp == hintPriority::Low) {
      debugc("[get_next_hint] : looking for a precision hint", 1);
      
      assert(trans.precision_hint.size() > 0);

      for(hintst::iterator it = trans.precision_hint.begin(); it != trans.precision_hint.end(); ++it) {
	solutiont new_hint;
      
	debugc("[get_next_hint] : precision hint = " << it->first, 0);
	candidate_hint = false;
      
	// some preceding decision might have rendered the hint or some of its conjuncts obsolete
	for(solutiont::iterator it1 = (it->first).begin(); it1 != (it->first).end(); ++it1) {
	  debugc("[get_next_hint] : hint conjunct = " << *it1, 1);
	
	  entailResult::s ret1 = abs.entails(*it1);

	  if (ret1 == entailResult::Incomplete) {
	      // candidate hints
	      new_hint.insert(*it1);
	      candidate_hint = true;
	      debugc("[get_next_hint] : precision candidate = " << *it1, 1);
	  }

	}

	// found a hint?
	if (candidate_hint) {
	  hint = std::make_pair(new_hint, it->second);
	  debugc("[get_next_hint] : (1) found precision hint " << hint, 1);
	  return hint;
	}
      }
      
      // reaching here means that there is no adequate hint
      assert(false);

    }
    else {

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
    }

    // ----no other option but returning a different priority hint
    debugc("[get_next_hint] : (2) hint = " << hint, 1);
    return hint;
  }

  hintt get_next_hint1(heapabs& abs, heaptrans& trans, downwardCompleteness::s complete) {
    hintt hint;
    bool firsthint = false;
    bool candidate_hint;

    debugc("[get_next_hint] : hints = " << trans.hint, 1);

    // propositional incompleteness or imprecise transformer?
    hintPriority::s hintp = (complete == downwardCompleteness::IncompleteProp) ? hintPriority::High : hintPriority::Low;

    debugc("[get_next_hint]", 0);

    if(hintp == hintPriority::Low) {
      debugc("[get_next_hint] : looking for a precision hint", 1);
      
      assert(trans.precision_hint.size() > 0);

      for(hintst::iterator it = trans.precision_hint.begin(); it != trans.precision_hint.end(); ++it) {
	solutiont new_hint;
      
	debugc("[get_next_hint] : precision hint = " << it->first, 0);
	candidate_hint = false;
      
	// some preceding decision might have rendered the hint or some of its conjuncts obsolete
	for(solutiont::iterator it1 = (it->first).begin(); it1 != (it->first).end(); ++it1) {
	  debugc("[get_next_hint] : hint conjunct = " << *it1, 1);
	
	  entailResult::s ret1 = abs.entails(*it1);

	  if (ret1 == entailResult::Incomplete) {
	      // candidate hints
	      new_hint.insert(*it1);
	      candidate_hint = true;
	      debugc("[get_next_hint] : precision candidate = " << *it1, 1);
	  }

	}

	// found a hint?
	if (candidate_hint) {
	  hint = std::make_pair(new_hint, it->second);
	  debugc("[get_next_hint] : (1) found precision hint " << hint, 1);
	  return hint;
	}
      }
     
      // reaching here means that there is no adequate hint
      assert(false);

    }
    else {

      int max_priority = 0;
      for(hintst::iterator it = trans.hint.begin(); it != trans.hint.end() /*&& !candidate_hint*/; ++it) {
	solutiont new_hint;
      
	debugc("[get_next_hint] : hint = " << it->first, 0);
	candidate_hint = false;

	// compute its weight
	unsigned int w = 0;
	for(literal_tablet::const_iterator lt_it = trans.literal_table.begin(); lt_it != trans.literal_table.end(); ++ lt_it) {
	  if(*(lt_it->first) == *((*((it->first).begin()))->lit)) {
	    w = (lt_it->second).size(); 
	    break;
	  }
	}
      
	if(w > max_priority || !firsthint) {
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
	    max_priority = w;
	    hint = std::make_pair(new_hint, w);
	    firsthint = true;
	  }
	
	  // the desired priority?
	  if (candidate_hint && /*it->second == hintp*/ w > max_priority) {
	    max_priority = w;
	    hint = std::make_pair(new_hint, w);
	    debugc("[get_next_hint] : (1) found hint with higher priority " << hint, 1);
	    //return hint;
	  }
	}
      }
    
      assert(firsthint == true);
    }

    // ----no other option but returning a different priority hint
    debugc("[get_next_hint] : (2) hint = " << hint, 1);
    return hint;
  }
  
  // return the weight for !hl
  unsigned int get_weight_neg(heaptrans& trans, heaplitp hl) {
    
    meetIrreduciblep mi = copy_lit(*hl);
    mi->complement();

    for(literal_tablet::const_iterator lt_it = trans.literal_table.begin(); lt_it != trans.literal_table.end(); ++ lt_it) 
      if(*(mi->lit) == *(lt_it->first)) {
	delete mi;
	return (lt_it->second).size(); 
      }

    delete mi;
    return 0;
  }

  hintt get_next_hint2(heapabs& abs, heaptrans& trans, downwardCompleteness::s complete) {
    hintt hint;
    bool firsthint = false;
    bool candidate_hint;

    debugc("[get_next_hint2] : hints = " << trans.hint, 1);

    // propositional incompleteness or imprecise transformer?
    hintPriority::s hintp = (complete == downwardCompleteness::IncompleteProp) ? hintPriority::High : hintPriority::Low;

    debugc("[get_next_hint2]", 0);

    if(hintp == hintPriority::Low) {
      debugc("[get_next_hint2] : looking for a precision hint", 1);
      
      assert(trans.precision_hint.size() > 0);

      for(hintst::iterator it = trans.precision_hint.begin(); it != trans.precision_hint.end(); ++it) {
	solutiont new_hint;
      
	debugc("[get_next_hint2] : precision hint = " << it->first, 0);
	candidate_hint = false;
      
	// some preceding decision might have rendered the hint or some of its conjuncts obsolete
	for(solutiont::iterator it1 = (it->first).begin(); it1 != (it->first).end(); ++it1) {
	  debugc("[get_next_hint] : hint conjunct = " << *it1, 1);
	
	  entailResult::s ret1 = abs.entails(*it1);

	  if (ret1 == entailResult::Incomplete) {
	      // candidate hints
	      new_hint.insert(*it1);
	      candidate_hint = true;
	      debugc("[get_next_hint2] : precision candidate = " << *it1, 1);
	  }

	}

	// found a hint?
	if (candidate_hint) {
	  hint = std::make_pair(new_hint, it->second);
	  debugc("[get_next_hint] : (1) found precision hint " << hint, 1);
	  return hint;
	}
      }
     
      // reaching here means that there is no adequate hint
      assert(false);

    }
    else {

      unsigned int max_priority = 0;
      debugc("[get_next_hint2] : literal_table = " << trans.literal_table, 1);
      
      for(literal_tablet::const_iterator lt_it = trans.literal_table.begin(); lt_it != trans.literal_table.end(); ++ lt_it) {
  	solutiont new_hint;
	unsigned int w;

	w = (lt_it->second).size() + get_weight_neg(trans, lt_it->first); 
	debugc("[get_net_hint2] : current weight = " << w, 1);
      
	if(w > max_priority || !firsthint) {
	  meetIrreduciblep mi = copy_lit(*(lt_it->first));
	  new_hint.insert(mi);
	  candidate_hint = true;

	  if (!firsthint) {
	    max_priority = w;
	    hint = std::make_pair(new_hint, w);
	    firsthint = true;
	  }
	
	  // the desired priority?
	  if (w > max_priority) {
	    max_priority = w;
	    hint = std::make_pair(new_hint, w);
	    debugc("[get_next_hint2] : found hint with higher weight" << hint, 1);
	  }
	}
      }

      assert(firsthint == true);
    }

    // ----no other option but returning a different priority hint
    debugc("[get_next_hint2] : hint = " << hint, 1);
    return hint;
  }



  int extrapolate (heapabs& sol, heaptrans& trans, downwardCompleteness::s complete) {
    hintt decision;

    debugc("Extrapolate", 1);
    assert (trans.literal_table.size() > 0 || trans.precision_hint.size() > 0);

    //debugc("[extrapolate]: hint before extrapolation = " << trans.hint, 0);

    decision = get_next_hint2(sol, trans, complete);

    //debugc("[extrapolate]: hint after extrapolation = " << trans.hint, 0);

    debugc("[extrapolate]: decision = " << decision.first << " and existent solution = " << sol, 0);

    formulat decision_f;

    // checking
    for(solutiont::iterator it = (decision.first).begin(); it!= (decision.first).end(); ++it) {
        clauset* newclause = new std::vector<heaplitp>();
	newclause->push_back((*it)->lit);
	decision_f.push_back(newclause);
    }

    entailResult::s res = sol.entails(&decision_f);
    assert(res == entailResult::Incomplete); 

    // adding the decision to the solution
    for(solutiont::iterator it = (decision.first).begin(); it!= (decision.first).end(); ++it) {
	sol.add_lit(*it);
	debugc("[extrapolate] : added to the solution : " << *it, 1);
	//inferenceRecord* ir = new inferenceRecord(*it, this);
	//sol.trail.insert(ir);

	// add all the affected clauses to potential_unit_clauses
	/* for(literal_tablet::const_iterator it1 = trans.literal_table.begin(); it1 != trans.literal_table.end(); ++it1) { */
	/*   if(*(it1->first) == *((*it)->lit)) */
	/*     trans.potential_unit_clauses.insert(trans.potential_unit_clauses.begin(), (it1->second).begin(), (it1->second).end()); */
	/* } */

    }
    

    inferenceRecord* ir = new inferenceRecord(*(decision.first.begin()), this);
    sol.trail.insert(ir);


    debugc("##################################################################", 1);
    debugc("[extrapolate]: Decision: " << decision_f, 1);
    debugc("##################################################################", 1);
    //sol.add_lit(decision.first);
    //inferenceRecord* ir = new inferenceRecord(decision.first, this);
    //sol.trail.insert(ir);

    // ---trans.hint.erase(decision);
    return 1;
    }

};

#endif

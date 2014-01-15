/*
** heaprefine.h
**
** Heap transformers refinement. 
**
*/

#include "heaptransformer.h"

#ifndef HEAPREFINE
#define HEAPREFINE

template <class abst, class transt, class heurt>
    struct heaprefine {

    public :

      downwardCompleteness::s construct (abst& abs, transt& trans, heurt& h) {
      	downwardCompleteness::s completeness;
      	transformerResult::s res;
	
      	do {
      	  do {
      	    res = trans.apply(abs);
	    //assert(trans.literal_table.size() > 0);
	    
      	    if (res & transformerResult::Bottom) {
	      debugc("[construct]: exit with Bottom", 1);
      	      return downwardCompleteness::Bottom;
      	    }
	    
      	  } while (res & transformerResult::CallAgain);
	  
	  //assert(trans.literal_table.size() > 0);

      	  // Check completeness
      	  completeness = trans.isComplete(abs);
      	  if (completeness == downwardCompleteness::Complete) {
            debugc("[construct]: exit with Complete", 1);
      	    return completeness;
      	  }
  	  debugc("[construct]: before extrapolation", 0);
      	  // Extrapolate
      	} while (h.extrapolate(abs, trans, completeness)); 
	
      	return downwardCompleteness::Unknown;
      }
      

      upwardCompleteness::s refine (abst& abs, transt& trans, heurt& h) {
	
      	debugc("Refine", 1);

	// reset
	trans.unit_clauses = trans.original_unit_clauses;
	trans.formula = trans.original_formula;
	trans.literal_table = trans.original_literal_table;

     	// Abstract
      	return h.interpolate(abs, trans);
      }
	
 
      transformerRefinementResult::s solve (abst& abs, transt& trans, heurt& h) {
    	downwardCompleteness::s constructionResult;
    	upwardCompleteness::s refinementResult;

	//trans.simplify_formula(abs);
	// backup
	trans.original_formula = trans.formula;
	trans.construct_literal_table();
	trans.original_literal_table = trans.literal_table;
	trans.original_unit_clauses = trans.unit_clauses;

	
	do {
          debugc("[solve]: Reset! ", 1);
	  abs.clear();
	  //trans.hint.clear();
	  trans.precision_hint.clear();
	  //trans.potential_unit_clauses.clear();
	  
	  //trans.reset = true;

	  //debugc("[solve]: hint after reset: " << trans.hint, 1);
	  debugc("[solve]: trail after reset: " << abs.trail, 0);
	  debugc("[solve] : literal_table = " << trans.literal_table, 1);

	  constructionResult = construct(abs, trans, h);

	  // print the trail;
	  debugc("[solve]: trail after construction phase: " << abs.trail, 1);

	  switch (constructionResult) {
	  default :      
	  case downwardCompleteness::IncompleteProp:
	  case downwardCompleteness::IncompleteTransformer:
	    assert(0);
	  case downwardCompleteness::Unknown: 
   	    debug("[solve]: exit with Unknown");
	    return transformerRefinementResult::Unknown;
	  case downwardCompleteness::Complete: 
   	    debug("[solve]: exit with NotBottom");
	    return transformerRefinementResult::NotBottom;
	  case downwardCompleteness::Bottom:
	    break;
	  }

	  refinementResult = refine(abs, trans, h);

	  switch (refinementResult) {
	  default : 
	  case upwardCompleteness::Incomplete:
	    assert(0);
	  case upwardCompleteness::Unknown: 
	    assert(0);
   	    //debug("[solve]: exit with Unknown after interpolation");
	    return transformerRefinementResult::Unknown;
	  case upwardCompleteness::Top:
	    //assert(0);
	    debug("[solve]: exit with Bottom after interpolation");
	    return transformerRefinementResult::Bottom;
	  case upwardCompleteness::Complete: 
	    break;
	  }
	  
	  //abs.setTop();

	} while (1);
	
	assert(0);
	return transformerRefinementResult::Unknown;
       }

    };

#endif

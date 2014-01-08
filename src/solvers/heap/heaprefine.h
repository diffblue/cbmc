/*
** heaprefine.h
**
** Heap transformers refinement. 
**
*/

/* #include <string> */
/* #include <iostream> */
/* #include <stdint.h> */
/* #include <assert.h> */
/* #include <set> */
/* #include <boost/shared_ptr.hpp> */

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
	    
      	    if (res & transformerResult::Bottom) {
	      debug("[construct]: exit with Bottom");
      	      return downwardCompleteness::Bottom;
      	    }
	    
      	  } while (res & transformerResult::CallAgain);
	  
	  
      	  // Check completeness
	  debugc("[construct]: before completeness check - abs.contents = " << abs.contents, 0);
      	  completeness = trans.isComplete(abs);
	  debugc("[construct]: after completeness check - abs.contents = " << abs.contents, 0);
      	  if (completeness != downwardCompleteness::Incomplete) {
            debug("[construct]: exit with Complete");
      	    return completeness;
      	  }
  	  debugc("[construct]: before extrapolation", 0);
	  debugc("[construct]: abs.contents = " << abs.contents, 0);
      	  // Extrapolate
      	} while (h.extrapolate(abs, trans)); ///h.extrapolate(abs);
	
      	return downwardCompleteness::Unknown;
      }
      

      upwardCompleteness::s refine (abst& abs, transt& trans, heurt& h) {
	
      	debug("Refine");
	
      	// Abstract
      	return h.interpolate(abs, trans);
      }
	
 
      transformerRefinementResult::s solve (abst& abs, transt& trans, heurt& h) {
    	downwardCompleteness::s constructionResult;
    	upwardCompleteness::s refinementResult;
	
	do {
          debug("[solve]: reset");
	  abs.clear();
	  trans.hint.clear();
	  //trans.simplify_formula(abs);
	  debugc("[solve]: formula after simplification: " << trans.formula, 1);
	  debugc("[solve]: hint after reset: " << trans.hint, 1);
	  debugc("[solve]: trail after reset: " << abs.trail, 0);
	  constructionResult = construct(abs, trans, h);
	  

	  // print the trail;
	  debugc("[solve]: trail after construction phase: " << abs.trail, 1);

	  switch (constructionResult) {
	  default :      
	  case downwardCompleteness::Incomplete:
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

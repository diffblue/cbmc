/*
** heaptransformer.h
**
** A heap theory & transformers. 
**
*/
#include "heapabstraction.h"
#include "heapwatches.h"
#include <sstream>
#include <string>

#ifndef HEAPTRANSFORMER
#define HEAPTRANSFORMER

class heaptrans {
 public:
    downwardCompleteness::s gamma;
    //hintst hint;
    hintst precision_hint;

    formulat formula;
    formulat original_formula;    

    clauset unit_clauses;
    clauset original_unit_clauses;

    literal_tablet original_literal_table;
    literal_tablet literal_table;

    //bool reset;

    // after full CBMC integration this can be removed
    ssa_countst* ssa_count;

    // todo: watches?
    // heapwatches watch;

    heaptrans() {
      precision_hint.clear();
      //reset = true;
      ssa_count = new ssa_countst;
    }

    heaptrans(formulat _formula) {
      precision_hint.clear();
      //reset = true;
      ssa_count = new ssa_countst;
      formula = _formula;
    }

    ~heaptrans () {
      for(formulat::const_iterator it = formula.begin(); it != formula.end(); ++it) {
	delete *it;
      }
      delete ssa_count;
    }

  // TRANSFORMERS & auxiliary functions


  entailResult::s check_constraint(formulat* constraint, heapabs& sol) {
    hintt h;
    entailResult::s res = sol.entails(constraint, h);

    if (res == entailResult::Incomplete) {
      debugc("[check_constraint] : gamma incomplete", 1);
      debugc("[check_constraint] : constraint = " << *constraint, 1);
      debugc("[check_constraint] : add hint " << h, 1);
      gamma = downwardCompleteness::IncompleteTransformer;
      debugc("[check_constraint] : (1) hints " << precision_hint, 1); 
      precision_hint.insert(h);
      debugc("[check_constraint] : (2) hints " << precision_hint, 1);
    }

    return res;
  }

  /*************************************************\
   *                                               *
   * transformer for mnew = free(m, v)             *
   *                                               *
  \*************************************************/
  /************************************************\
   * transformer for  mnew = free(m, v) with      *
   *    respect to v1 = sel(m, v2, f)             *
  \************************************************/
  bool ded_free_sel(heapvar m, heapvar mnew, heapvar v,
		    heapvar v1, heapvar v2,
		    heapvar f, heapabs& sol) {

    formulat* constraint = and_("ll", not_equal(v1, heapexpr(v)),
				not_equal(v2, heapexpr(v)));

    entailResult::s ret = check_constraint(constraint, sol);
    delete constraint;
 
    switch(ret) {
    case entailResult::True:
      return sol.add_eq(v1, heapexpr(v2, mnew, f), stateTrue);
    case entailResult::False:
    case entailResult::Incomplete:
    default: 
      return false;
    }

  }

  /*******************************************************************************\
   * transformer for  mnew = free(m, v) with respect to !(v1 = sel(m, v2, f))    *
  \*******************************************************************************/
  bool ded_free_not_sel(heapvar m, heapvar mnew, heapvar v,
			heapvar v1, heapvar v2,
			heapvar f, heapabs& sol) {

    formulat* constraint = and_("ll", not_equal(v1, heapexpr(v)),
				not_equal(v2, heapexpr(v)));

    entailResult::s ret = check_constraint(constraint, sol);
    delete constraint;
 
    switch(ret) {
    case entailResult::True:
      return sol.add_eq(v1, heapexpr(v2, mnew, f), stateFalse);
    case entailResult::False:
    case entailResult::Incomplete:
    default: 
      return false;
    }
  }

  /*****************************************************************************\
   * transformer for  mnew = free(m, v) with respect to Path(m, v1, v2, f)     *
  \*****************************************************************************/
  bool ded_free_path(heapvar m, heapvar mnew, heapvar v,
		     heapvar v1, heapvar v2, 
		     heapvar f, heapabs& sol) {

    // constraint under which new facts are to be deducted
    formulat* constraint = and_("lll", path(m, v1, v, f),
				path(m, v, v2, f),
				not_path(m, v2, v, f));


    debugc("[ded_free_path]", 1);
    entailResult::s ret = check_constraint(constraint, sol);
    delete constraint;

    switch(ret) {
    case entailResult::False:
      return sol.add_path(mnew, v1, v2, f, stateTrue);
    case entailResult::True:
    case entailResult::Incomplete:
    default: 
      return false;
    }
  }

  /***************************************************************************\
   * transformer for  mnew = free(m, v) with respect to !Path(m, v1, v2, f)  *
  \***************************************************************************/
  bool ded_free_not_path(heapvar m, heapvar mnew, heapvar v,
			 heapvar v1, heapvar v2, 
			 heapvar f, heapabs& sol) {

    formulat* constraint = and_("ll", not_equal(v1, heapexpr(v)),
				not_equal(v2, heapexpr(v)));

    entailResult::s ret = check_constraint(constraint, sol);
    delete constraint;

    switch (ret) {
    case entailResult::True:
      return sol.add_path(mnew, v1, v2, f, stateFalse);
    case entailResult::False:
    case entailResult::Incomplete:
    default: 
      return false;
    }
  }

  /********************************************************************************\
   * transformer for  mnew = free(m, v) with respect to Dangling(m, v1)           *
  \********************************************************************************/
  bool ded_free_dangling(heapvar m, heapvar mnew, heapvar v,
			 heapvar v1, heapabs& sol) {

    return sol.add_dangling(mnew, v1, stateTrue);

  }


  /*********************************************************************************\
   * general transformer for  mnew = free(m, v)                                    *
  \*********************************************************************************/
  bool ded_free(heaplitp hl, heapabs& sol) {
    bool callAgain = false;
    heapvar v = hl->x;
    heapvar m = hl->m;
    heapvar mnew = hl->mnew;
    heapvar mpath;
    heapvar f = hl->f;

    /********************************************************************************\
     * transfer phase                                                               *
    \********************************************************************************/
    heapvar v3, v4;

    adj_listt::const_iterator adj_list_it = sol.adj_list.find(m);

    if(adj_list_it != sol.adj_list.end()) {
      // for the affected memory configuration
      for(mem_adj_listt::const_iterator it = (adj_list_it->second).begin(); it != (adj_list_it->second).end(); ++it) {
    	for(fld_adj_listt::const_iterator it1 = (it->second).begin(); it1 != (it->second).end(); ++it1) {
    	  v3 = (*it1).first;
    	  targetst targets = (*it1).second;
    	  for(targetst::const_iterator it2 = targets.begin(); it2 != targets.end(); ++it2) {
    	    v4 = *it2;
    	    callAgain |= ded_free_path(m, mnew, v, v3, v4, f, sol);
    	  }
    	}
      }
    }

    for(not_pathst::const_iterator it = sol.not_paths.begin(); it != sol.not_paths.end(); ++it) {
      mpath = (*it)->m;
      if(mpath == m) {
    	v3 = (*it)->x;
    	v4 = (*it)->y;
    	callAgain |= ded_free_not_path(m, mnew, v, v3, v4, f, sol);
      }
    }

    
    for(sel_eqst::iterator it = sol.sel_eqs.begin(); it != sol.sel_eqs.end(); ++it)
      if((it->second).m == m) {
    	callAgain |= ded_free_sel(m, mnew, v, it->first, (it->second).v, (it->second).f, sol);
      }

    for(not_eqst::iterator it = sol.not_eqs.begin(); it != sol.not_eqs.end(); ++it)
      if((it->second).is_sel() && (it->second).m == m) {
    	callAgain |= ded_free_not_sel(m, mnew, v, (it->second).v, it->first, (it->second).f, sol);
      }

    /********************************************************************************\
     * generation phase: generate Dangling(mnew, v)                                 *
    \********************************************************************************/
    callAgain |= sol.add_dangling(mnew, v, stateTrue);


    if (callAgain) {
      debugc("[ded_free]: transformerResult::CallAgain", 1);
    }
    else {
      debugc("[ded_free]: transformerResult::DoNotCallAgain", 1);
    }


    return callAgain;
  }

  /*********************************************************************************\
   *                                                                               *
   * transformer for v1.f = v2 <=> mnew = store(m, v1, f, v2)                      *
   *                                                                               *
  \*********************************************************************************/

  /**********************************************************************************\
   * transformer for  mnew = store(m, v1, f, v2) with respect to v4 = sel(m, v3, f) *
  \**********************************************************************************/
  bool ded_store_sel(heapvar m, heapvar mnew, heapvar v1,
  		     heapvar v2, heapvar v3, heapvar v4,
  		     heapvar f, heapabs& sol) {

    formulat* constraint = and_("ll", equal(v1, heapexpr(v3)),
				not_equal(v2, heapexpr(v4)));

    debugc("[ded_store_sel] : " << v4 << " = sel(" << m << ", "
	   << v3 << ", " << f << ")", 1);
    entailResult::s ret = check_constraint(constraint, sol);
    debugc("[ded_store_sel] : constraint = " << *constraint, 1);
    delete constraint;
 
    switch(ret) {
    case entailResult::True:
      debugc("[ded_store_sel] : constraint satisfied", 1);
      return sol.add_eq(v4, heapexpr(v3, mnew, f), stateFalse);
    case entailResult::False:
      debugc("[ded_store_sel] : constraint not satisfied ", 1);
      return sol.add_eq(v4, heapexpr(v3, mnew, f), stateTrue);
    case entailResult::Incomplete:
    default: 
      return false;
    }
  }
  
  /************************************************************************************\
   * transformer for  mnew = store(m, v1, f, v2) with respect to !(v4 = sel(m, v3, f))*
  \************************************************************************************/

  bool ded_store_not_sel(heapvar m, heapvar mnew, heapvar v1,
			 heapvar v2, heapvar v3, heapvar v4,
			 heapvar f, heapabs& sol) {

    formulat* constraint = and_("ll", equal(v1, heapexpr(v3)),
				equal(v2, heapexpr(v4)));

    debugc("[ded_store_sel]", 1);

    entailResult::s ret = check_constraint(constraint, sol);
    delete constraint;

    switch(ret) {
    case entailResult::True:
      return sol.add_eq(v4, heapexpr(v3, mnew, f), stateTrue);
    case entailResult::False:
      return sol.add_eq(v4, heapexpr(v3, mnew, f), stateFalse);
    case entailResult::Incomplete:
    default: 
      return false;
    }
  }

  /*********************************************************************************\
   * transformer for  mnew = store(m, v1, f, v2) with respect to Path(m, v3, v4, f)*
  \*********************************************************************************/
  bool ded_store_path(heapvar m, heapvar mnew, heapvar v1,
  		      heapvar v2, heapvar v3, heapvar v4,
  		      heapvar f, heapabs& sol) {

    // constraint under which new facts are to be deduced
    formulat* constraint = and_("llll", path(m, v3, v1, f),
				path(m, v1, v4, f),
				not_path(m, v4, v1, f),
				not_path(m, v2, v4, f),
				not_equal(v1, heapexpr(v4)));

    debugc("[ded_store_path]", 1);

    entailResult::s ret = check_constraint(constraint, sol);
    debugc("[ded_store_path]: path( " << m << ", " << v3 << ", " << v4 << ")", 1);
    debugc("[ded_store_path]: constraint = " << *constraint, 0);
    debugc("[ded_store_path]: checkconstraint is " << ret, 0);
    debugc("[ded_store_path]: entailResult::True = " << entailResult::True, 0);
    debugc("[ded_store_path]: entailResult::False = " << entailResult::False, 0);

    delete constraint;

    switch(ret) {
    case entailResult::True:
      debugc("[ded_store_path]: add path( " << mnew << ", " << v3 << ", " << v4 << ", false)", 1);
      return sol.add_path(mnew, v3, v4, f, stateFalse);
    case entailResult::False:
      debugc("[ded_store_path]: add path( " << mnew << ", " << v3 << ", " << v4 << ", true)", 1);
      return sol.add_path(mnew, v3, v4, f, stateTrue);
    case entailResult::Incomplete:
    default: 
      return false;
    }

  }

  /************************************************************************************\
   * transformer for  mnew = store(m, v1, f, v2) with respect to !Path(m, v3, v4, f)  *
  \************************************************************************************/
  bool ded_store_not_path(heapvar m, heapvar mnew, heapvar v1,
  			  heapvar v2, heapvar v3, heapvar v4,
  			  heapvar f, heapabs& sol) {

    formulat* constraint = and_("lll", path(m, v3, v1, f),
				path(m, v2, v4, f),
				not_equal(v1, heapexpr(v4)));

    debugc("[ded_store_not_path]", 1);

    entailResult::s ret = check_constraint(constraint, sol);
    delete constraint;

    switch (ret) {
    case entailResult::True:
      debugc("[ded_store_not_path]: add path( " << mnew << ", " << v3 << ", " << v4 << ", true)", 1);
      return sol.add_path(mnew, v3, v4, f, stateTrue);
    case entailResult::False:
      debugc("[ded_store_not_path]: add path( " << mnew << ", " << v3 << ", " << v4 << ", false)", 1);
      return sol.add_path(mnew, v3, v4, f, stateFalse);
    case entailResult::Incomplete:
    default: 
      return false;
    }
  }


  /*******************************************************************\
   * transformer for  mnew = store(m, v1, f, v2) with respect to     *
   * Dangling(m, v3) and !Dangling(m, v3)                            *
  \*******************************************************************/
  bool ded_store_dangling(heapvar m, heapvar mnew, heapvar v1,
			  heapabs& sol) {
  
    return sol.add_dangling(mnew, v1, stateTrue);
  }

  bool ded_store_not_dangling(heapvar m, heapvar mnew, heapvar v1,
			      heapabs& sol) {
  
    return sol.add_dangling(mnew, v1, stateFalse);
  }

  /******************************************************************\
   * general transformer for  mnew = store(m, v1, f, v2)            *
  \******************************************************************/
  bool ded_store(heaplitp hl, heapabs& sol) {
    bool callAgain = false;
    heapvar v1, v2, m, mnew, f, mpath, fpath;
    heapvar v3, v4;
    v1 = hl->x;
    v2 = hl->y;
    m = hl->m;
    mnew = hl->mnew;
    f = hl->f;

    adj_listt::const_iterator adj_list_it = sol.adj_list.find(m);

    if(adj_list_it != sol.adj_list.end()) {
      // for the affected memory configuration
      for(mem_adj_listt::const_iterator it = (adj_list_it->second).begin(); it != (adj_list_it->second).end(); ++it) {
	for(fld_adj_listt::const_iterator it1 = (it->second).begin(); it1 != (it->second).end(); ++it1) {
	  v3 = (*it1).first;
	  targetst targets = (*it1).second;
	  for(targetst::const_iterator it2 = targets.begin(); it2 != targets.end(); ++it2) {
	    v4 = *it2;
	    // field sensitivity
	    if(!(it->first == f)) {
	      callAgain |= sol.add_path(mnew, v3, v4, it->first, stateTrue);
	      debugc("[ded_store] : (1) callAgain = " << callAgain, 1);
	    }
	    else {
	      callAgain |= ded_store_path(m, mnew, v1, v2, v3, v4, f, sol);
      	      debugc("[ded_store] : (2) callAgain = " << callAgain, 1);
	    }
	  }
	}
      }
    }

    for(not_pathst::const_iterator it = sol.not_paths.begin(); it != sol.not_paths.end(); ++it) {
      mpath = (*it)->m;
      if(mpath == m) {
	fpath = (*it)->f;
	v3 = (*it)->x;
	v4 = (*it)->y;

	if(!(f == fpath)) {
	  callAgain |= sol.add_path(mnew, v3, v4, fpath, stateFalse);
	  debugc("[ded_store] : (3) callAgain = " << callAgain, 1);
	}
	else {
	  callAgain |= ded_store_not_path(m, mnew, v1, v2, v3, v4, f, sol);
	  debugc("[ded_store] : (4) callAgain = " << callAgain, 1);
	}
      }
    }

    
    for(sel_eqst::iterator it = sol.sel_eqs.begin(); it != sol.sel_eqs.end(); ++it) 
      if((it->second).m == m) {
	if ((it->second).f == f) {
	  callAgain |= ded_store_sel(m, mnew, v1, v2, (it->second).v, it->first, (it->second).f, sol);
	  debugc("[ded_store] : (5) callAgain = " << callAgain, 1);	  
	}
	else {
	  callAgain |= sol.add_eq(it->first, heapexpr((it->second).v, mnew, (it->second).f), stateTrue);
	  debugc("[ded_store] : (6) callAgain = " << callAgain, 1);
	}
      }

    for(not_eqst::iterator it = sol.not_eqs.begin(); it != sol.not_eqs.end(); ++it) 
      if((it->second).is_sel() && (it->second).m == m) {
	if ((it->second).f == f) {
	  callAgain |= ded_store_not_sel(m, mnew, v1, v2, (it->second).v, it->first, (it->second).f, sol);
	  debugc("[ded_store] : (7) callAgain = " << callAgain, 1);
	}
	else {
  	  callAgain |= sol.add_eq(it->first, heapexpr((it->second).v, mnew, (it->second).f), stateFalse);
	  debugc("[ded_store] : (8) callAgain = " << callAgain, 1);	  
	}
      }

    heapexpr* tmp = new heapexpr(hl->x, hl->mnew, hl->f);
    callAgain |= ded_eq(new eq_lit(hl->y, *tmp, stateTrue), sol);

    if (callAgain) {
      debugc("[ded_store]: transformerResult::CallAgain", 1);
    }
    else {
      debugc("[ded_store]: transformerResult::DoNotCallAgain", 1);
    }

    return callAgain;

  }

  /******************************************************************\
   *                                                                *
   * transformer for mnew = new(m, v)                               *
   *                                                                *
  \******************************************************************/
  bool ded_new(const heaplitp hl, heapabs& sol) const {
    bool callAgain = false;
    heapvar v3, v4, v5, m, mnew, mpath, fpath;
    m = hl->m;
    mnew = hl->mnew;

    /****************************************************************\
     * transfer phase: transfer all the abstract elements referring *
     * to the previous heap configuration                           *
    \****************************************************************/

    adj_listt::const_iterator adj_list_it = sol.adj_list.find(m);

    if(adj_list_it != sol.adj_list.end()) {
      // for the affected memory configuration
      for(mem_adj_listt::const_iterator it = (adj_list_it->second).begin(); it != (adj_list_it->second).end(); ++it) {
	for(fld_adj_listt::const_iterator it1 = (it->second).begin(); it1 != (it->second).end(); ++it1) {
	  v3 = (*it1).first;
	  targetst targets = (*it1).second;
	  for(targetst::const_iterator it2 = targets.begin(); it2 != targets.end(); ++it2) {
	    v4 = *it2;
	    callAgain |= sol.add_path(mnew, v3, v4, it->first, stateTrue);
	  }
	}
      }
    }

   for(not_pathst::const_iterator it = sol.not_paths.begin(); it != sol.not_paths.end(); ++it) {
      mpath = (*it)->m;
      if(mpath == m) {
	fpath = (*it)->f;
	v3 = (*it)->x;
	v4 = (*it)->y;
	callAgain |= sol.add_path(mnew, v3, v4, fpath, stateFalse);
      }
    }

    for(sel_eqst::iterator it = sol.sel_eqs.begin(); it != sol.sel_eqs.end(); ++it) 
      if((it->second).m == m)
	callAgain |= sol.add_eq(it->first, heapexpr((it->second).v, mnew, (it->second).f), stateTrue);

    for(not_eqst::iterator it = sol.not_eqs.begin(); it != sol.not_eqs.end(); ++it) 
      if((it->second).is_sel() && (it->second).m == m)
	callAgain |= sol.add_eq(it->first, heapexpr((it->second).v,  mnew, (it->second).f), stateFalse);



    /****************************************************************\
     * generation phase: generate disiqualities between the new var *
     * and all the existing ones                                    *
    \****************************************************************/
    std::set<heapvar> var = this->get_vars_before(hl);
    heapvar v = hl->x;
    for(std::set<heapvar>::const_iterator it = var.begin(); it != var.end(); ++it) {
      if (!(v == *it)) {
	heapexpr* tmp = new heapexpr();
	tmp->make_var(*it);
	heaplitp hl = new eq_lit(v, *tmp, stateFalse);
	debugc("[ded_new] : hl = " << hl, 1);
	callAgain |= sol.add_lit(hl);
      }
    }

    /****************************************************************\
     * generation phase: generate newvar != null                    *
    \****************************************************************/
    heapexpr* tmp = new heapexpr();
    tmp->make_nil();
    callAgain |= sol.add_lit(new eq_lit(v, *tmp, stateFalse));

    if (callAgain) {
      debugc("[ded_new]: transformerResult::CallAgain", 1);
    }
    else {
      debugc("[ded_new]: transformerResult::DoNotCallAgain", 1);
    }


    return callAgain;

  }

  /****************************************************************\
   *                                                              *
   * transformer for mnew = m                                     *
   *                                                              *
  \****************************************************************/
  bool ded_mem_eq(const heaplitp hl, heapabs& sol) const {
    bool callAgain = false;
    heapvar v3, v4, v5, m, mnew, mpath, fpath;
    m = hl->m;
    mnew = hl->mnew;

    /*************************************************************\
     * transfer phase: transfer all the abstract elements        *
     * referring to the previous heap configuration              *
    \*************************************************************/
 
    adj_listt::const_iterator adj_list_it = sol.adj_list.find(m);

    if(adj_list_it != sol.adj_list.end()) {
      // for the affected memory configuration
      for(mem_adj_listt::const_iterator it = (adj_list_it->second).begin(); it != (adj_list_it->second).end(); ++it) {
	for(fld_adj_listt::const_iterator it1 = (it->second).begin(); it1 != (it->second).end(); ++it1) {
	  v3 = (*it1).first;
	  targetst targets = (*it1).second;
	  for(targetst::const_iterator it2 = targets.begin(); it2 != targets.end(); ++it2) {
	    v4 = *it2;
	    callAgain |= sol.add_path(mnew, v3, v4, it->first, stateTrue);
	  }
	}
      }
    }

    for(not_pathst::const_iterator it = sol.not_paths.begin(); it != sol.not_paths.end(); ++it) {
      mpath = (*it)->m;
      if(mpath == m) {
	fpath = (*it)->f;
	v3 = (*it)->x;
	v4 = (*it)->y;
	callAgain |= sol.add_path(mnew, v3, v4, fpath, stateFalse);
      }
    }

    for(sel_eqst::iterator it = sol.sel_eqs.begin(); it != sol.sel_eqs.end(); ++it) 
      if((it->second).m == m)
	callAgain |= sol.add_eq(it->first, heapexpr((it->second).v, mnew, (it->second).f), stateTrue);

    for(not_eqst::iterator it = sol.not_eqs.begin(); it != sol.not_eqs.end(); ++it) 
      if((it->second).is_sel() && (it->second).m == m)
	callAgain |= sol.add_eq(it->first, heapexpr((it->second).v,  mnew, (it->second).f), stateFalse);


    if (callAgain) {
      debugc("[ded_mem_eq]: transformerResult::CallAgain", 1);
    }
    else {
      debugc("[ded_mem_eq]: transformerResult::DoNotCallAgain", 1);
    }

    return callAgain;
  }

  /***************************************************************\
   *                                                             *
   * transformer for Path(m, v1, v2, f)                          *
   *                                                             *
  \***************************************************************/
  bool ded_path(const heaplitp hl, heapabs& sol) const {

    // generation phase: add the new fact to the solution
    bool callAgain = sol.add_lit(copy_lit(*hl));

    if (callAgain) {
      debugc("[ded_path]: transformerResult::CallAgain", 1);
    }
    else {
      debugc("[ded_path]: transformerResult::DoNotCallAgain", 1);
    }

    return callAgain;

  }

  /***************************************************************\
   *                                                             *
   * transformer for Onpath(m, v1, v2, v3, f)                    *
   *                                                             *
  \***************************************************************/
  /* bool ded_onpath(const heaplitp hl, heapabs& sol) const { */

  /*   // generation phase: add the new fact to the solution */
  /*   return sol.add_lit(copy_lit(*hl)); */
  /* } */


  /***************************************************************\
   *                                                             *
   * transformer for Dangling(m, v)                              *
   *                                                             *
  \***************************************************************/
  bool ded_dangling(const heaplitp hl, heapabs& sol) const {

    // generation phase: add the new fact to the solution
    bool callAgain = sol.add_lit(copy_lit(*hl));

    if (callAgain) {
      debugc("[ded_dangling]: transformerResult::CallAgain", 1);
    }
    else {
      debugc("[ded_dangling]: transformerResult::DoNotCallAgain", 1);
    }

    return callAgain;

  }

  /***************************************************************\
   *                                                             *
   * transformer for v = e                                       *
   *                                                             *
  \***************************************************************/
  bool ded_eq(const heaplitp hl, heapabs& sol) const {
    bool callAgain = false;

    if((hl->rhs).is_sel() && hl->state == stateTrue) 
      callAgain |= sol.add_lit(new path_lit((hl->rhs).m, (hl->rhs).v, hl->x, (hl->rhs).f, stateTrue));

    // add the new fact to the solution
    callAgain |= sol.add_lit(copy_lit(*hl));

    if (callAgain) {
      debugc("[ded_eq]: transformerResult::CallAgain", 1);
    }
    else {
      debugc("[ded_eq]: transformerResult::DoNotCallAgain", 1);
    }

    return callAgain;
  }

  bool apply_one_ded(heaplitp& unit, heapabs& sol) {

    bool callAgain = false;

    debugc("unit clause:" << unit, 1);
    debugc("************************************************", 1);
    debugc("Transformer " << unit << ":", 1);
    debugc("************************************************", 1);
    switch(unit->type) {
    case PATH:
      callAgain |= ded_path(unit, sol);;
      break;
    case ONPATH:
      /* callAgain |= ded_onpath(unit, sol); */
      break;
    case NEW:
      callAgain |= ded_new(unit, sol);
      break;
    case EQ:
      callAgain |= ded_eq(unit, sol);
      break;
    case FREE:
      callAgain |= ded_free(unit, sol);
      break;
    case STORE:
      callAgain |= ded_store(unit, sol);
      break;
    case DANGLING:
      callAgain |= ded_dangling(unit, sol);
      break;
    case MEMEQ:
      callAgain |= ded_mem_eq(unit, sol);
      break;
    case NO_TERM:;
    default:;  
    }
    debugc("sol = " << sol, 1);

    inferenceRecord* ir = new inferenceRecord(new meetIrreducible(unit), this);
    sol.trail.insert(ir);

    return callAgain;
  }

  // the main transformer
  transformerResult::s apply(heapabs& sol) {
    bool callAgain = false;
    gamma = downwardCompleteness::Complete;
    heaplitp unit;
    bool unitb;

    //assert(literal_table.size() > 0);

    debugc("[apply]: solution = " << sol, 1);
    debugc("[apply]: formula size = " << formula.size(), 0);

    debugc("[apply] : Apply the unit clauses already computed: ", 1);
    for(clauset::iterator it = unit_clauses.begin(); it != unit_clauses.end(); ++it)
      callAgain |= apply_one_ded(*it, sol);

    debugc("[apply] : Check the enabled clauses: ", 1);

    literal_tablet tmp_literal_table;
    tmp_literal_table.clear();

    //assert(literal_table.size() > 0);
    assert(tmp_literal_table.size() == 0);

    //bool keep_record = false;

    for(literal_tablet::iterator it = literal_table.begin(); it != literal_table.end(); ++it) {
      heaplitp hl = it->first;
      meetIrreduciblep mi = new meetIrreducible(hl);
      //formulat tmp_literal_record;
      //tmp_literal_record.clear();

      switch(sol.entails(mi)) {
      case entailResult::True:
	// enabled
	debugc("[apply] : enabled clauses for mi = " << *mi, 1);
	for(formulat::iterator it1 = (it->second).begin(); it1 != (it->second).end(); ++it1) {
	  if(unit_clause(*it1, unit, sol)) {
	    debugc("[apply]: found new enabled unit clause " << *unit, 1);
	    callAgain |= apply_one_ded(unit, sol);

	    // early bottom detection for equalities and inequalities
	    if  (sol.is_early_bottom()) {
	      debugc("[apply] : Early bottom detected! ", 1);
	      return transformerResult::Bottom;
	    }

	    unit_clauses.push_back(unit);
	   }
	  /*else {
	    tmp_literal_record.push_back(*it1);
	    }*/
	  
	}
	// still clauses to be watched for the current literal
	/*	if(tmp_literal_record.size() > 0) {
	  // create a new record
	  literal_recordt lr = std::make_pair(hl, tmp_literal_record);
	  tmp_literal_table.push_back(lr);
	  keep_record = true;
	  }*/

	break;
      case entailResult::False:
	// clauses already satisfied
	break;
      default:
	// keep the record
	debugc("[apply] : keep record " << *it, 1);
	tmp_literal_table.push_back(*it);
	//assert(tmp_literal_table.size() > 0);
	//keep_record = true;
      }
    }

    //assert(!(tmp_literal_table.size() == 0 && keep_record));
    
    //assert(tmp_literal_table.size() > 0);

    literal_table = tmp_literal_table;

    //assert(literal_table.size() > 0);

    debugc("transformerResult: " << (int)callAgain, 0);

    debugc("[apply] : Did we reach bottom? ", 1);
    if  (sol.is_bottom()) {
      debugc("[apply] : Bottom detected! ", 1);
      return transformerResult::Bottom;
    }

    debugc("[apply]: trail: " << sol.trail, 0);

    if (callAgain) {
      debugc("[apply]: Transformer result is CallAgain", 1);
      return transformerResult::CallAgain;
    }

    debugc("[apply]: transformerResult::DoNotCallAgain", 1);
    return transformerResult::DoNotCallAgain;
  }


  // gamma completeness depends on both the abstraction and the transformers
  downwardCompleteness::s isComplete(heapabs& sol) const {
    bool satisfied = true;
   
    debugc("[isComplete]: gamma completeness check ", 1);
    // each clause is satisfied
    for(formulat::const_iterator it1 = formula.begin(); satisfied && it1 != formula.end(); ++it1) {
      satisfied = false;
      debugc("[isComplete]: now trying clause " << **it1, 1);
      debugc("[isComplete]: trail = " << sol.trail, 0);
      for(clauset::const_iterator it2 = (*it1)->begin(); it2 != (*it1)->end(); ++it2) {
      	//if (satisfied)
	//break;

	heaplitp hl = *it2;
	if(hl->type == EQ || hl->type == PATH || hl->type == ONPATH || hl->type == DANGLING) {
	  // check if the literal is true
	  if(sol.entails_literal(hl)) {
	    satisfied = true;
	    break;
	  }
	}
	else {
	  // check if the clause was applied
	  for(trailt::const_iterator it3 = sol.trail.begin(); it3 != sol.trail.end(); ++it3) {
	    if (**it2 == *((*it3)->inference->lit)) {
	      debugc("[isComplete]: clause satisfied: " << **it1, 1);
	      satisfied = true;
	      break;
	    }
	  }
	}
      }
    }
    debugc("[isComplete]: end of completeness test ", 0);

    // has been applied for each clause  
    if (!satisfied) {
      debugc("[isComplete] : incomplete (1) ", 1);
      return downwardCompleteness::IncompleteProp;
    }

    // take into consideration the precision of the abstract transformer
    return gamma; 
  }

  //================================================
  // loops
  //================================================
  
  /* void apply_unit(heaplitp& unit, heapabs& sol, transformerResult::s& ret) { */
  /*    transformerResult::s transformer_ret; */

  /*   switch(unit->type) { */
  /*   case PATH: */
  /*     transformer_ret = ded_path(unit, sol); */
  /*     ret = transformerResult::OrCallAgain(transformer_ret, ret); */
  /*     break; */
  /*   case ONPATH: */
  /*     transformer_ret = ded_onpath(unit, sol); */
  /*     ret = transformerResult::OrCallAgain(transformer_ret, ret); */
  /*     break; */
  /*   case NEW: */
  /*     transformer_ret = ded_new(unit, sol); */
  /*     ret = transformerResult::OrCallAgain(transformer_ret, ret); */
  /*     break; */
  /*   case EQ: */
  /*     //case ASSIGN:   */
  /*     transformer_ret = ded_eq(unit, sol); */
  /*     ret = transformerResult::OrCallAgain(transformer_ret, ret); */
  /*     break; */
  /*   case FREE: */
  /*     transformer_ret = ded_free(unit, sol); */
  /*     ret = transformerResult::OrCallAgain(transformer_ret, ret); */
  /*     break; */
  /*   case STORE: */
  /*     /\* transformer_ret = ded_store(unit, sol); *\/ */
  /*     /\* ret = transformerResult::OrCallAgain(transformer_ret, ret); *\/ */
  /*     /\* break; *\/ */
  /*   case DANGLING: */
  /*     transformer_ret = ded_dangling(unit, sol); */
  /*     ret = transformerResult::OrCallAgain(transformer_ret, ret); */
  /*     break; */
  /*   case MEMEQ: */
  /*     transformer_ret = ded_mem_eq(unit, sol); */
  /*     ret = transformerResult::OrCallAgain(transformer_ret, ret); */
  /*     break; */
  /*   case NO_TERM:; */
  /*   default:; */
  /*   } */

  /*   return; */
  /* } */


  /* void remove_constraints(const std::set<heapvar>& vars, solutiont& sol, solutiont& new_sol) { */
  /*     for(solutiont::const_iterator it2 = sol.begin(); it2 != sol.end(); ++it2) { */
  /* 	heaplitp hl = (*it2)->lit; */
  /* 	std::set<heapvar> hlvars = hl->get_vars();  */
  /* 	bool found = false; */

  /* 	for(std::set<heapvar>::const_iterator it1 = vars.begin(); it1 != vars.end(); ++it1) { */
  /* 	  heapvar v = *it1; */
  /* 	  debugc("[remove_constraints] : trying " << hl << " with " << v << " with vars " << hlvars, 0); */

  /* 	  if(hlvars.find(v) != hlvars.end()) { */
  /* 	    debugc("[remove_constraints] : removing " << hl, 0); */
  /* 	    found = true; */
  /* 	    //sol.erase(*it2); */
  /* 	  } */
  /* 	} */
  /* 	if (!found) */
  /* 	  new_sol.insert(*it2); */
  /*     } */
  /* } */

  /* void invalidate_constraints(heaplitp& unit, heapabs& sol) { */
  /*   std::set<heapvar> vars; */
  /*   solutiont new_sol; */

  /*   debugc("[invalidate_constraints]: constraints before invalidation: " << sol, 0); */

  /*   switch(unit->type) { */
  /*   case NEW: */
  /*   case FREE: */
  /*   case STORE: */
  /*   case EQ:   */
  /*     vars.clear(); */
  /*     vars.insert(unit->x); */
  /*     new_sol.clear(); */
  /*     remove_constraints(vars, sol.contents, new_sol); */
  /*     sol.contents = new_sol; */
  /*     break; */
  /*   case MEMEQ: */
  /*     vars.clear(); */
  /*     vars.insert(unit->mnew); */
  /*     new_sol.clear(); */
  /*     remove_constraints(vars, sol.contents, new_sol); */
  /*     sol.contents = new_sol; */
  /*     break; */
  /*   case PATH: */
  /*   case ONPATH:   */
  /*   case DANGLING: */
  /*   case NO_TERM:; */
  /*   default:; */
  /*   } */

  /*   debugc("[invalidate_constraints]: constraints after invalidation: " << sol, 0); */
    
  /* } */

  /* void copy_solution(solutiont& source, solutiont& dest) { */

  /*   for(solutiont::const_iterator it = source.begin(); it != source.end(); ++it) { */
  /*     meetIrreduciblep mi = new_meetIrreducible((*it)->lit); */
  /*     dest.insert(mi); */
  /*   } */
  /* } */

  /* bool change(solutiont& initial, solutiont& final) { */

  /*   for(solutiont::const_iterator it = final.begin(); it != final.end(); ++it) { */
  /*     if (initial.find(*it) == initial.end()) */
  /* 	return true; */
  /*   } */

  /*   return false; */
  /* } */


  /* void apply_loop(heapabs& sol, const formulat& init, const std::set<heapvar>& tmp_vars) { */
  /*   transformerResult::s ret = transformerResult::DoNotCallAgain; */
  /*   heaplitp unit; */
  /*   solutiont initial_sol; */

  /*   do { */
  /*   ret = transformerResult::DoNotCallAgain; */

  /*   // loop init */
  /*   for(unsigned int i = 0; i < init.size(); ++i) { */
  /*     bool unitb = unit_clause(init[i], unit, sol); */
  /*     if(unitb) { */
  /* 	apply_unit(unit, sol, ret); */
  /*     } */
  /*   } */


  /*   // now the TC transformer is applied after initialization as well as literals might be removed  */
  /*   std::cout << "************************************************" << std::endl; */
  /*   std::cout << "Transformer TC (initialization):" << std::endl; */
  /*   std::cout << "************************************************" << std::endl; */
  /*   ret =  transformerResult::OrCallAgain(ded_tc(sol), ret); */
  /*   debug(sol); */
  /*   } while(ret == transformerResult::CallAgain); */


  /*   if  (sol.is_bottom()) { */
  /*     ret = transformerResult::Bottom; */
  /*     debug("Bottom detected"); */
  /*   } */

  /*   debugc("[apply_loop]: inv after initialization = " << sol, 1); */

  /*   do { */
  /*     copy_solution(sol.contents, initial_sol); */

  /* 	// loop body */
  /* 	for(unsigned int i = 0; i < formula.size(); ++i) { */
  /* 	  // don't care about the result now */
  /* 	  //transformerResult::s transformer_ret; */

  /* 	  bool unitb = unit_clause(formula[i], unit, sol); */
  /* 	  if(unitb) { */

  /*   	    if(!(unit->is_pure()))  */
  /* 	      invalidate_constraints(unit, sol); */

  /* 	    do { */
  /* 	    ret = transformerResult::DoNotCallAgain; */
  /* 	    std::cout << "************************************************" << std::endl; */
  /* 	    std::cout << "Transformer (inside loop) " << unit << ":" << std::endl; */
  /* 	    std::cout << "************************************************" << std::endl; */


  /* 	    apply_unit(unit, sol, ret); */
  /* 	    debugc("[apply_loop]: sol = " << sol, 1); */
	    
  /* 	    // now the TC transformer is applied after each other transformer as literals might be removed  */
  /* 	    std::cout << "************************************************" << std::endl; */
  /* 	    std::cout << "Transformer TC (inside loop):" << std::endl; */
  /* 	    std::cout << "************************************************" << std::endl; */
  /* 	    ret =  transformerResult::OrCallAgain(ded_tc(sol), ret); */
  /* 	    debug(sol); */
  /* 	    } while(ret == transformerResult::CallAgain); */
 
  /* 	  } */
  /* 	  else { */
  /* 	    // decisions can be made inside the loop as well */
  /* 	    add_hints(formula[i], sol); */
  /* 	  } */
  /* 	} */
  /* 	debugc("[apply_loop] : remove constraints for " << tmp_vars, 1); */
  /* 	solutiont new_sol; */
  /* 	new_sol.clear(); */
  /* 	remove_constraints(tmp_vars, sol.contents, new_sol); */
  /* 	sol.contents = new_sol; */
  /* 	debugc("[apply_loop] : previous solution = " << initial_sol, 1); */
  /* 	debugc("[apply_loop] : current solution = " << sol.contents, 1); */
  /* 	debugc("[apply_loop] : new_sol = " << new_sol, 1); */

  /*   } while (change(initial_sol, sol.contents)); */
  /*   /\* if  (sol.is_bottom()) { *\/ */
  /*   /\*   ret = transformerResult::Bottom; *\/ */
  /*   /\*   debug("Bottom detected"); *\/ */
  /*   /\* } *\/ */

  /*   //debugc("[apply]: trail: " << sol.trail, 0); */
  /*   debugc("[apply]: hint: " << sol.hint, 0); */
  /*   return; */
  /* } */

  formulat* and_(std::string, ...) const;
  clauset* or_(const heaplitp, const heaplitp) const;
  clauset* or_(const heaplitp, const heaplitp, const heaplitp) const;
  clauset* or_(const heaplitp, const heaplitp, const heaplitp, const heaplitp) const;

  formulat* copy_formula(formulat*);

  formulat* complement_clause(clauset*);
  formulat* complement_formula(formulat*);

  formulat* distribute_disj(formulat*, formulat*);
  //formulat* process_conditional(formulat*, formulat*, formulat*);
  formula_ssat* process_conditional(formulat*, formula_ssat*, formula_ssat*);
  //formulat* process_loop(formulat*, formulat*);

  std::vector<std::pair<heapvar, int> >* ssa_literal(heaplitp);
  ssa_countst* ssa(formulat*);

  // return the set of memory vars in the formula
  std::set<heapvar> get_mems() const;
  // return the set of pointer vars in the formula
  std::set<heapvar> get_vars() const;
  std::set<heapvar> get_vars_before(heaplit*) const;

  static formulat* insert_lit_in_formula(const heaplitp, formulat*);
  formulat* insert_clause_in_formula(formulat*, clauset*);
  void insert_literal(const heaplitp);
  void insert_clause(clauset*);
  void clear ();

  bool equal_clauses (const clauset*, const clauset*, heapabs&);
  bool pure_literal(const heaplitp) const;

  bool formula_contains_literal(const heaplitp, heapabs&);
  bool single_literal(const clauset*, const heaplitp) const;

  // add the pure literals in clause c as hints
  //void add_hints(const clauset*, heapabs&);

  //bool hint_heuristic(clauset*&,  heapabs&);
  //bool hint_heuristic_aggressive(clauset*&, heapabs&, hintst::iterator);

  //void set_hint(heaplitp&, clauset*&, heapabs&);
  bool unit_clause (clauset*&, heaplitp&, heapabs&);
  clauset* create_disjunction(std::vector< meetIrreduciblep >&);

  //bool hint_contains(const meetIrreduciblep&) const;
  clauset* simplify_clause (clauset*, heapabs&);
  void simplify_formula (heapabs&);

  void construct_literal_table();
  void add_to_literal_table(clauset*&);

}; 

std::ostream& operator<< (std::ostream&, const heaptrans&);
std::ostream& operator<< (std::ostream&, const std::set<heapvar>&);

#endif

  

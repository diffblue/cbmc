/*
** heapabs.h
**
** A heap abstraction. 
**
*/

#include "heapliteral.h"
#include <iostream>

#ifndef TRP_HEAPABS
#define TRP_HEAPABS
 

class heapabs {
public :
  trailt trail;

  // positive heap facts:
  // equivalence classes
  aliasest aliases; 
  // reachability graph
  adj_listt adj_list;
  // eqs of the form v1 = sel(m, v2, n)
  sel_eqst sel_eqs;

  // negative heap facts
  not_eqst not_eqs;
  not_pathst not_paths;

  heapabs () {
    aliases.clear();
    adj_list.clear();
    sel_eqs.clear();
  }

  entailResult::s entails(const meetIrreduciblep& e) {
    entailResult::s ret = entailResult::Incomplete;

    debugc("[entails] : (0)", 0);

    debugc("[entails] : (1) e = " << e, 0);

    if (entails_literal(e)) 
      return entailResult::True;

    debugc("[entails] : (2)", 0);

    e->complement();

    debugc("[entails] : (3)", 0);

    if (entails_literal(e))
      ret = entailResult::False;		     

    debugc("[entails] : (4)", 0);

    e->complement();

    debugc("[entails] : (5)", 0);

    return ret;
  }

  entailResult::s entails(formulat* f, hintt& h) {
    entailResult::s ret = entailResult::True;

    solutiont new_hint;
    new_hint.clear();

    for(formulat::const_iterator it = f->begin(); it != f->end(); ++it) {
      if(entails(*it, new_hint) == entailResult::Incomplete) 
	ret = entailResult::Incomplete;
      if(entails(*it, new_hint) == entailResult::False) {
	h = std::make_pair(new_hint, /*hintPriority::Low*/0);
	return entailResult::False;
      }
    }

    h = std::make_pair(new_hint, /*hintPriority::Low*/0);
    return ret;
  }

  entailResult::s entails(formulat* f) {
    entailResult::s ret = entailResult::True;

    solutiont new_hint;
    new_hint.clear();

    for(formulat::const_iterator it = f->begin(); it != f->end(); ++it) {
      if(entails(*it, new_hint) == entailResult::Incomplete) 
	ret = entailResult::Incomplete;
      if(entails(*it, new_hint) == entailResult::False) {
	return entailResult::False;
      }
    }

    return ret;
  }


  bool add_lit(meetIrreduciblep mi) {
    debugc("[add_lit] : mi = " << mi, 0);
    return add_lit(mi->lit);
  }

  bool add_lit(heaplitp hl) {
    debugc("[add_lit] : hl = " << hl, 0);
    switch(hl->type) {
    case PATH:
      return add_path(hl->m, hl->x, hl->y, hl->f, hl->state);
    case ONPATH:
      //return add_onpath(hl->m, hl->x, hl->y, hl->z, hl->f, hl->state);
      break;
    case EQ:
      return add_eq(hl->x, hl->rhs, hl->state);
    case DANGLING:
      return add_dangling(hl->m, hl->x, hl->state);
    default:
      assert(1 == 0);
      return false;
    }
   
  }

  bool add_path(heapvar m, heapvar x, heapvar y, heapvar f, uint8_t s) {
    fld_adj_listt fal;
    mem_adj_listt mal;
    targetst targets;

    fal.clear();
    mal.clear();
    targets.clear();

    // get the representatives
    heapvar x_ = aliases.find(x);
    heapvar y_ = aliases.find(y);

    debugc("[add_path] : add path(" << m << ", " << x << ", " << y << ", " << f << ")", 1);
    debugc("[add path] : x_ = :" << x_, 0); 
    debugc("[add path] : y_ = :" << y_, 0); 
    debugc("[add path] : adj list :" << adj_list, 0); 

    if(s == stateTrue) {
      // locate the adj list corresponding to the memory configuration m
      adj_listt::iterator adj_list_it = adj_list.find(m);

      if(adj_list_it == adj_list.end()) {
	// no adj list for the mem configuration m
	targets.insert(y_);
	fal[x_] = targets;
	mal[f] = fal;
	adj_list[m] = mal;
	debugc("[add path] : 1. adj list after insertion:" << adj_list, 0);
	return true;
      }

      // locate the adj list corresponding to the field f
      mem_adj_listt::iterator mem_adj_list_it = (adj_list_it->second).find(f);

      if(mem_adj_list_it == (adj_list_it->second).end()) {
	targets.insert(y_);
	fal[x_] = targets;
	(adj_list_it->second)[f] = fal;
	debugc("[add path] : 2. adj list after insertion:" << adj_list, 0);
	return true;
      }

      // locate the targets for x
      fld_adj_listt::iterator fld_adj_list_it = (mem_adj_list_it->second).find(x_);

      if(fld_adj_list_it == (mem_adj_list_it->second).end()) {
	targets.insert(y_);
	(mem_adj_list_it->second)[x_] = targets;
	//debugc("[add path] : adj list after insertion:" << adj_list, 1);
	return true;
      }

      targetst::iterator targets_it = (fld_adj_list_it->second).find(y_);
      if (targets_it != (fld_adj_list_it->second).end()) {
	debugc("[add_path] : no change ", 0);
	return false;
      }

      (fld_adj_list_it->second).insert(y_);
      // debugc("[add path] : adj list after insertion:" << adj_list, 1);
      return true;
    }
    else {
      heaplitp hl = new path_lit(m, x_, y_, f, s);
      debugc("[add_path/not] : add " << hl, 0);
      if(not_paths.find(hl) != not_paths.end()) {
	//delete hl;
	debugc("[add_path] : no change", 0);
	return false;
      }
      not_paths.insert(hl);
      debugc("[add_path/not] : not_paths = " << not_paths, 0);
      return true;
    }
  }

  bool add_dangling(heapvar m, heapvar x, uint8_t s) {
    return add_eq(x, heapexpr(heapvar("dangling")), s);
  }

  bool add_eq(heapvar x, heapexpr y, uint8_t s) {
    bool ret;
    sel_eqst tmp_sel_eqs;

    tmp_sel_eqs.clear();

    debugc("[add_eq] adding x = " << x << " and y = " << y << " and state = " << (int)s, 1);

    if(s == stateTrue) {
      heapvar old_x = aliases.find(x);
      heapvar old_y = aliases.find(y.v);

      debugc("[add_eq] : x = " << x << " and old_x = " << old_x, 1);
      debugc("[add_eq] : y.v = " << y.v << " and old_y = " << old_y, 1);

      if(y.is_sel()) {
	not_eqt seleq = std::make_pair(old_x, heapexpr(old_y, y.m, y.f));
	if(sel_eqs.find(seleq) != sel_eqs.end())
	  return false;

	if(!(old_x == aliases.find(heapvar()))) {
	   // assume non-circularity
	  not_eqt noteq = std::make_pair(old_x, heapexpr(old_y));
	  not_eqs.insert(noteq);
	}

	debugc("[add_eq] : adding sel_eq " << seleq, 1);
	sel_eqs.insert(seleq);
	

	// check whether sel_eqs generates any new equality
	// todo : change the equiv classes to store heapexpr and remove this..
	for(sel_eqst::iterator sel_eqs_it = sel_eqs.begin(); sel_eqs_it != sel_eqs.end(); ++sel_eqs_it) {
	  heapexpr sel1 = sel_eqs_it->second;
	  debugc("[add_eq] : found sel_eq (1) " << *sel_eqs_it, 0);
	  for(sel_eqst::iterator it = sel_eqs.begin(); it != sel_eqs.end(); ++it) {
	    if(sel_eqs_it != it && sel1 == it->second) {
	      debugc("[add_eq] : found sel_eq (2) " << *it, 0);
	      // todo: add_eq also modifies sel_eqs...
	      debugc("[add_eq] : add eq (6) " << sel_eqs_it->first << " = " << heapexpr(it->first), 1);
	      tmp_sel_eqs.insert(std::make_pair(sel_eqs_it->first, heapexpr(it->first)));

	      //add_eq(sel_eqs_it->first, heapexpr(it->first), stateTrue);
	    }
	  }
	}

	for(sel_eqst::const_iterator it = tmp_sel_eqs.begin(); it != tmp_sel_eqs.end(); ++it) 
	  add_eq(it->first, it->second, stateTrue);


       // check whether sel_eqs generates any new disequality
       // todo : change the equiv classes to store heapexpr and remove this..
       /* for(sel_eqst::iterator sel_eqs_it = sel_eqs.begin(); sel_eqs_it != sel_eqs.end(); ++sel_eqs_it) { */
       /* 	 debugc("[add_eq] : adding not_eq coz of " << *sel_eqs_it, 1); */
       /* 	 add_eq(sel_eqs_it->first, heapexpr((sel_eqs_it->second).v), stateFalse); */
       /* } */

       return true;
      }

      debugc("[add_eq]: make_union " << x << " and " << y.v, 1);
      ret = aliases.make_union(x, y.v);
      
      if(ret) {
	debugc("[add_eq] : no change", 0);
	return false;
      }

      // get the new representative for x and y
      heapvar new_x = aliases.find(x);

      debugc("[add_eq] : old_x = " << old_x, 0);
      debugc("[add_eq] : old_y = " << old_y, 0);
      debugc("[add_eq] : new_x = " << new_x, 0);

      // collapse facts in the reachability graph
      for(adj_listt::iterator adj_list_it = adj_list.begin(); adj_list_it != adj_list.end(); ++adj_list_it) 
	for(mem_adj_listt::iterator mem_adj_list_it = (adj_list_it->second).begin(); mem_adj_list_it != (adj_list_it->second).end(); ++mem_adj_list_it) {
	  if (!(old_x == new_x)) {
	    fld_adj_listt::iterator old_x_it = (mem_adj_list_it->second).find(old_x);
	    if (old_x_it != (mem_adj_list_it->second).end()) {
	      fld_adj_listt::iterator new_x_it = (mem_adj_list_it->second).find(new_x);
      	      if (new_x_it != (mem_adj_list_it->second).end()) {
		(new_x_it->second).insert((old_x_it->second).begin(), (old_x_it->second).end());
		(mem_adj_list_it->second)[new_x] = new_x_it->second;
	      }
	      else {
		(mem_adj_list_it->second)[new_x] = old_x_it->second;
	      }
	      (mem_adj_list_it->second).erase(old_x_it);
	    }
	  }
	  if (!(old_y == new_x)) {
	    debugc("[add_eq] : collapse facts for old_y = " << old_y << " and new_x = " << new_x, 0);
	    fld_adj_listt::iterator old_y_it = (mem_adj_list_it->second).find(old_y);
    	    if (old_y_it != (mem_adj_list_it->second).end()) {
	      fld_adj_listt::iterator new_x_it = (mem_adj_list_it->second).find(new_x);
       	      if (new_x_it != (mem_adj_list_it->second).end()) {
		(new_x_it->second).insert((old_y_it->second).begin(), (old_y_it->second).end());
		(mem_adj_list_it->second)[new_x] = new_x_it->second;
	      }
	      else {
		(mem_adj_list_it->second)[new_x] = old_y_it->second;
		debugc("[add_path] : updated " << mem_adj_list_it->second, 0);
	      }
	      (mem_adj_list_it->second).erase(old_y_it);
	    }
	    debugc("[add_eq] : after update adj_list = " << adj_list, 0);
	  }
	}

      // rename the targets in the reachability graph
      for(adj_listt::iterator adj_list_it = adj_list.begin(); adj_list_it != adj_list.end(); ++adj_list_it) 
	for(mem_adj_listt::iterator mem_adj_list_it = (adj_list_it->second).begin(); mem_adj_list_it != (adj_list_it->second).end(); ++mem_adj_list_it) 
	  for(fld_adj_listt::iterator fld_adj_list_it = (mem_adj_list_it->second).begin(); fld_adj_list_it != (mem_adj_list_it->second).end(); ++fld_adj_list_it) {
	    if (!(old_x == new_x)) {
	      targetst::iterator targets_it = (fld_adj_list_it->second).find(old_x);  
	      if(targets_it != (fld_adj_list_it->second).end()) {
		(fld_adj_list_it->second).erase(targets_it);
		(fld_adj_list_it->second).insert(new_x);
	      }
	    }
	    if (!(old_y == new_x)) {
	      targetst::iterator targets_it = (fld_adj_list_it->second).find(old_y);  
	      if(targets_it != (fld_adj_list_it->second).end()) {
		(fld_adj_list_it->second).erase(targets_it);
		(fld_adj_list_it->second).insert(new_x);
	      }
	    }

	  }


      not_eqst tmp_not_eqs = not_eqs;

       // update not_eqs 
      for(not_eqst::iterator not_eqs_it = tmp_not_eqs.begin(); not_eqs_it != tmp_not_eqs.end(); ++not_eqs_it) {
	debugc("[add_eq] : not_eq = " << *not_eqs_it, 1);
	if(!(old_x == new_x)) {
	  not_eqt noteq;
	  if(not_eqs_it->first == old_x) {
	    noteq = *not_eqs_it;
	    not_eqs.erase(*not_eqs_it);
	    noteq.first = new_x;
	    debugc("[add_eq]: add not_eq (1) " << noteq, 1);
	    not_eqs.insert(noteq);
	  }
	  if((not_eqs_it->second).v == old_x) {
	    noteq = *not_eqs_it;
	    not_eqs.erase(*not_eqs_it);
	    noteq.second.v = new_x;
	    debugc("[add_eq]: add not_eq (2) " << noteq, 1);
	    not_eqs.insert(noteq);
	  }
	}
	if(!(old_y == new_x)) {
	  if(not_eqs_it->first == old_y) {
	    not_eqt noteq = *not_eqs_it;
	    not_eqs.erase(*not_eqs_it);
	    noteq.first = new_x;
	    debugc("[add_eq]: add not_eq (3) " << noteq, 1);
	    not_eqs.insert(noteq);
	  }
	  if((not_eqs_it->second).v == old_y) {
	    not_eqt noteq = *not_eqs_it;
	    not_eqs.erase(*not_eqs_it);
	    noteq.second.v = new_x;
	    debugc("[add_eq]: add not_eq (4) " << noteq, 1);
	    not_eqs.insert(noteq);
	  }
	}
      }


      sel_eqst tmp_sel_eqs = sel_eqs;

       // update sel_eqs 
      for(sel_eqst::iterator sel_eqs_it = tmp_sel_eqs.begin(); sel_eqs_it != tmp_sel_eqs.end(); ++sel_eqs_it) {
	if(!(old_x == new_x)) {
	  if(sel_eqs_it->first == old_x) {
	    not_eqt sel_eq = *sel_eqs_it;
	    sel_eqs.erase(*sel_eqs_it);
	    sel_eq.first = new_x;
	    sel_eqs.insert(sel_eq);
	  }
	  if((sel_eqs_it->second).v == old_x) {
	    not_eqt sel_eq = *sel_eqs_it;
	    sel_eqs.erase(*sel_eqs_it);
	    sel_eq.second.v = new_x;
	    sel_eqs.insert(sel_eq);
	  }
	}
	if(!(old_y == new_x)) {
	  if(sel_eqs_it->first == old_y) {
	    not_eqt sel_eq = *sel_eqs_it;
	    sel_eqs.erase(*sel_eqs_it);
	    sel_eq.first = new_x;
	    sel_eqs.insert(sel_eq);
	  }
	  if((sel_eqs_it->second).v == old_y) {
	    not_eqt sel_eq = *sel_eqs_it;
	    sel_eqs.erase(*sel_eqs_it);
	    sel_eq.second.v = new_x;
	    sel_eqs.insert(sel_eq);
	  }
	}
      }

      // check whether sel_eqs generates any new equality
      // todo : change the equiv classes to store heapexpr and remove this..

      tmp_sel_eqs.clear();
      for(sel_eqst::iterator sel_eqs_it = sel_eqs.begin(); sel_eqs_it != sel_eqs.end(); ++sel_eqs_it) {
	heapexpr sel1 = sel_eqs_it->second;
	for(sel_eqst::iterator it = sel_eqs.begin(); it != sel_eqs.end(); ++it) {
	  if(sel_eqs_it != it && sel1 == it->second) {
	    // todo: add_eq also modifies sel_eqs...
	    //add_eq(sel_eqs_it->first, heapexpr(it->first), stateTrue);
	    tmp_sel_eqs.insert(std::make_pair(sel_eqs_it->first, heapexpr(it->first)));
	  }
	}
      }

      for(sel_eqst::const_iterator it = tmp_sel_eqs.begin(); it != tmp_sel_eqs.end(); ++it) 
	add_eq(it->first, it->second, stateTrue);


      debugc("[add_eq/not_paths] : not_paths = " << not_paths, 1);
       // update not_paths 
      for(not_pathst::iterator not_paths_it = not_paths.begin(); not_paths_it != not_paths.end(); ++not_paths_it) {
	if(!(old_x == new_x)) {
	  if((*not_paths_it)->x == old_x) {
	    debugc("[add_eq/not_path] : replacing old_x = " << old_x, 0);
	    heaplitp not_path = *not_paths_it;
	    not_paths.erase(not_paths_it);
	    not_path->x = new_x;
	    not_paths.insert(not_path);
	    debugc("[add_eq/not_path] : after replacement not_paths = " << not_paths, 0);
	  }
	  if((*not_paths_it)->y == old_x) {
	    debugc("[add_eq/not_path] : replacing old_x = " << old_x, 0);
	    heaplitp not_path = *not_paths_it;
	    not_paths.erase(not_paths_it);
	    not_path->y = new_x;
	    not_paths.insert(not_path);
	    debugc("[add_eq/not_path] : after replacement not_paths = " << not_paths, 0);
	  }
	}
	if(!(old_y == new_x)) {
	  if((*not_paths_it)->x == old_y) {
	    debugc("[add_eq/not_path] : replacing old_y = " << old_y, 0);
	    heaplitp not_path = *not_paths_it;
	    not_paths.erase(not_paths_it);
	    not_path->x = new_x;
	    not_paths.insert(not_path);
	    debugc("[add_eq/not_path] : after replacement not_paths = " << not_paths, 0);
	  }
	  if((*not_paths_it)->y == old_y) {
	    debugc("[add_eq/not_path] : replacing old_y = " << old_y, 0);
	    heaplitp not_path = *not_paths_it;
	    not_paths.erase(not_paths_it);
	    not_path->y = new_x;
	    not_paths.insert(not_path);
	    debugc("[add_eq/not_path] : after replacement not_paths = " << not_paths, 0);
	  }
	}
      }

      return true;

    }
    else {
      // find the representatives
      heapvar x_ = aliases.find(x);
      heapvar y_ = aliases.find(y.v);

      if(not_eqs.find(std::make_pair(x_, heapexpr(y_, y.m, y.f))) != not_eqs.end())
	return false;

      not_eqt noteq = std::make_pair(x_, heapexpr(y_, y.m, y.f)); 
      debugc("[add_eq]: add not_eq (5) " << noteq, 1);
      not_eqs.insert(noteq);
      return true;
    }

  }


  void clear() {
    trail.clear();
    not_eqs.clear();
    adj_list.clear();
    not_paths.clear();
    sel_eqs.clear();
    aliases.clear();
  }


   // is the current solution bottom?
   bool is_bottom() {

    debugc("[is_bottom] adj_list = " << adj_list, 1);


    for(not_pathst::const_iterator it = not_paths.begin(); it != not_paths.end(); ++it) {
      heaplitp hl = *it;
      debugc("[is_bottom] : try " << hl, 1);
      debugc("[is_bottom] : hl->x = " << aliases.find(hl->x) << " and hl->y = " << aliases.find(hl->y), 1);
      if (entails_path(hl->m, hl->x, hl->y, hl->f)) {
	debugc("[is_bottom] : contradiction for " << hl, 1);
	debugc("[is_bottom] : hl->x = " << aliases.find(hl->x) << " and hl->y = " << aliases.find(hl->y), 0);
	return true;
      }
    }

    for(not_eqst::iterator it = not_eqs.begin(); it != not_eqs.end(); ++it) {
      not_eqt eq = *it;
      if (entails_eq(eq.first, eq.second)) {
	debugc("[is_bottom] : contradiction for " << eq.first << " != " << eq.second, 1);
	return true;
      }
    }


    return false;
  }


   // is the current solution bottom?
   // early detection for eq
   bool is_early_bottom() {
     for(not_eqst::iterator it = not_eqs.begin(); it != not_eqs.end(); ++it) {
       not_eqt eq = *it;
       if (entails_eq(eq.first, eq.second)) {
	 debugc("[is_early_bottom] : contradiction for " << eq.first << " != " << eq.second, 1);
	 return true;
       }
     }


     return false;
   }



  /* downwardCompleteness::s isComplete() const { */
  /*   return gamma; */
  /* } */

  bool entails_literal(const heaplitp& hl) {
    debugc("[entails_literal]: hl = " << hl, 0);

    debugc("[entails_literal] : type = " << hl->type, 0);
    //assert(hl->type == EQ || hl->type == PATH || hl->type == ONPATH || hl->type == DANGLING);
    
    switch(hl->type) {
    case EQ:
      bool res;
      if(hl->state == stateTrue) {
	res = entails_eq(hl->x, hl->rhs);
	debugc("[entails_literal] : (1) res = " << res, 0);
      }
      else {
	res = entails_not_eq(hl->x, hl->rhs);
	debugc("[entails_literal] : (2) res = " << res, 0);
      }
      return res;
    case PATH:
      if(hl->state == stateTrue)
	return entails_path(hl->m, hl->x, hl->y, hl->f);
      return entails_not_path(hl->m, hl->x, hl->y, hl->f);
    case ONPATH:
      /* if(hl->state == stateTrue) */
      /* 	return entails_onpath(hl->m, hl->x, hl->y, hl->z, hl->f); */
      /* return entails_not_onpath(hl->m, hl->x, hl->y, hl->z, hl->f); */
      break;
    case DANGLING:
      if(hl->state == stateTrue)
	return entails_dangling(hl->m, hl->x);
      return entails_not_dangling(hl->m, hl->x);
    default:
      for(trailt::const_iterator it3 = trail.begin(); it3 != trail.end(); ++it3) {
	if (*hl == *((*it3)->inference->lit)) {
	  debugc("[entails_literal]: literal found " << hl, 1);
	  return true;
	}
      }
      return false;
    }
  } 


 protected:


  bool entails_eq(const heapvar hv1, const heapvar he2) {
    return entails_eq(hv1, heapexpr(he2));
  }

  bool entails_eq(const heapvar he1, const heapexpr he2) {
    heapvar m_ = aliases.find(he2.m);
    heapvar he2_ = aliases.find(he2.v);
    heapvar he1_ = aliases.find(he1);

    if(he2.is_sel()) {
      debugc("[is_eq/sel] : sel_eqs = " << sel_eqs, 1);
      not_eqt hl = std::make_pair(he1_, heapexpr(he2_, m_, he2.f));
      return sel_eqs.find(hl) != sel_eqs.end();
    }

    return he1_ == he2_;
  }

  bool entails_not_eq(const heapvar he1, const heapexpr he2) {

    debugc("[entails_not_eq] : he1 = " << he1 << " and he2 = " << he2, 0);

    // find the representatives
    heapvar m_ = aliases.find(he2.m);
    heapvar he1_ = aliases.find(he1);
    heapvar he2_ = aliases.find(he2.v);

    debugc("[entails_not_eq] : he1 = " << he1_ << " and he2 = " << he2_, 0);

    for(not_eqst::const_iterator it = not_eqs.begin(); it != not_eqs.end(); ++it) {
      if (it->first == he1_ && it->second == heapexpr(he2_, m_, he2.f))
	return true;
      if (!he2.is_sel() && it->first == he2_ && it->second == heapexpr(he1_))
	return true;
    }

    return false;
  }

  // exists a path from hv1 to hv2 in the memory configuration m
  bool entails_path(heapvar m, heapvar hv1, heapvar hv2, heapvar f) {
    
    // get the representatives
    heapvar hv1_ = aliases.find(hv1);
    heapvar hv2_ = aliases.find(hv2);

    debugc("[entails_path] : path(" << m << ", " << hv1 << ", " << hv2 << ", " << f << ")", 1);
    debugc("[entails_path] : hv1_ = :" << hv1_, 0); 
    debugc("[entails_path] : hv2_ = :" << hv2_, 0); 

    // trivially true path
    if (hv1_ == hv2_)
      return true;

    debugc("[entails_path] : adj_lit : " << adj_list, 0);

    // locate the corresponding reachability subgraph
    adj_listt::iterator it1 = adj_list.find(m);
    if(it1 == adj_list.end())
      return false;

    mem_adj_listt::iterator it2 = (it1->second).find(f);

    if(it2 == (it1->second).end())
      return false;

    // BFS
    std::vector<heapvar> q;
    q.clear();
    std::set<heapvar> visited;
    visited.clear();

    // start the exploration with the representative of hv1
    q.push_back(hv1_);

    while (!q.empty()) {
      heapvar tmp = q.back();
      q.pop_back();
      
      if(visited.find(tmp) != visited.end())
	continue;

      visited.insert(tmp);

      debugc("[entails_path] : current element processesed = " << tmp, 0);
      //debugc("[entails_path] : queue after popping = " << q, 1);

      // did i find the target?
      if (tmp == hv2_) {
	debugc("[entails_path] : target found " << tmp, 0);
        return true;
      }

      debugc("[entails_path] : " << tmp << " != " << hv2_, 0);

      // search for the current node's targets
      fld_adj_listt::iterator it3 = (it2->second).find(tmp);

      if(it3 == (it2->second).end()) 
	continue;

      targetst targets = it3->second;
      debugc("[entails_path] : add targets " << targets, 0);

      for(targetst::iterator it4 = targets.begin(); it4 != targets.end(); ++it4) 
	q.push_back(*it4);

    }

    return false;
  }

  bool entails_not_path(heapvar m, heapvar hv1, heapvar hv2, heapvar f) {
    // get the representatives
    heapvar hv1_ = aliases.find(hv1);
    heapvar hv2_ = aliases.find(hv2);

    debugc("[entails_not_path] : path(" << m << ", " << hv1 << ", " << hv2 << ", " << f << ", false)", 1);
    debugc("[entails_not_path] : hv1_ = :" << hv1_, 0); 
    debugc("[entails_not_path] : hv2_ = :" << hv2_, 0); 
    debugc("[entails_not_path] : not_paths = :" << not_paths, 0); 

    for(not_pathst::const_iterator it = not_paths.begin(); it != not_paths.end(); ++it) {
      heaplitp hl = *it;
      if ((m == hl->m) && (f == hl->f) && 
	  ((hv1_ == hl->x && hv2_ == hl->y) ||
	   (hv2_ == hl->x && hv1_ == hl->y)))
	return true;
    }
    return false;
  }

  bool entails_dangling(heapvar m, heapvar hv1) {
    return aliases.find(hv1) == aliases.find(heapvar("dangling"));
  } 

  bool entails_not_dangling(heapvar m, heapvar hv1) {
    return !(aliases.find(hv1) == aliases.find(heapvar("dangling")));
  } 

  bool entails_literal(const meetIrreduciblep& e) {
    return entails_literal(e->lit);
  }


  entailResult::s entails(clauset* f, solutiont& h) {
    meetIrreduciblep m;
    entailResult::s ret = entailResult::False;

    for(clauset::const_iterator it = f->begin(); it != f->end(); ++it) {
      m = new meetIrreducible(*it);
      switch(entails(m)) {
      case entailResult::True:
	return entailResult::True;
      case entailResult::False:
	if(ret == entailResult::False)
	  ret = entailResult::False;
	break;
      case entailResult::Incomplete:
	ret = entailResult::Incomplete;
	// record the element as a hint
	h.insert(m);
      default:;
      }
    }

    return ret;
  }


};

std::ostream& operator<< (std::ostream&, const heapabs&); 

#endif

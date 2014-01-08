#include "heaptransformer.h"
#include <cstdarg>

std::ostream& operator<< (std::ostream& s, const heaptrans& h) {
  s << "F = ";
  formulat f = h.formula;
  
  s << f;

  s << std::endl;
  return s;
}

// returns the conjunction of literals/clauses
// fmt contains l for a literal to be added, and c for a clause
formulat* heaptrans::and_(std::string fmt, ...) const {
  va_list args;
  formulat* f = new formulat;
  int i = 0;
    
  va_start(args, fmt);
  while (fmt[i] != '\0') {
    if (fmt[i] == 'l') {
      heaplitp hl = va_arg(args, heaplitp);
      f = heaptrans::insert_lit_in_formula(hl, f);
    } 
    else {
      assert(fmt[i] == 'c');
      clauset* c = va_arg(args, clauset*);
      f->push_back(c);
    }
    i++;
  }
  va_end(args);
  return f;
}

clauset* heaptrans::or_(const heaplitp hl1, const heaplitp hl2) const {
  clauset* f = new clauset;
    
  f->push_back(hl1);
  f->push_back(hl2);
  return f;
}

clauset* heaptrans::or_(const heaplitp hl1, const heaplitp hl2, const heaplitp hl3) const {
  clauset* f = new clauset;

  f->push_back(hl1);
  f->push_back(hl2);
  f->push_back(hl3);
  return f;
}

clauset* heaptrans::or_(const heaplitp hl1, const heaplitp hl2, const heaplitp hl3, const heaplitp hl4) const {
  clauset* f = new clauset;

  f->push_back(hl1);
  f->push_back(hl2);
  f->push_back(hl3);
  f->push_back(hl4);
  return f;
}

  
formulat* heaptrans::complement_clause(clauset* c) {
  formulat *res = new formulat;

  for (clauset::iterator it = c->begin(); it != c->end(); ++it) {
    heaplitp hl = (copy_lit(**it))->lit;
    hl->complement();
    res = heaptrans::insert_lit_in_formula(hl, res);
  }
  debugc("[complement_clause]: res = " << *res, 1);
  return res;
}


formulat* heaptrans::copy_formula(formulat* f) {
  formulat* res = new formulat;

  for(formulat::const_iterator it1 = f->begin(); it1 != f->end(); ++it1) {
    clauset* c = new clauset;

    for(clauset::const_iterator it2 = (*it1)->begin(); it2 != (*it1)->end(); ++it2) {
      heaplitp hl = (copy_lit(**it2))->lit;
      c->push_back(hl);
    }

    res->push_back(c);
  }

  return res;
}


formulat* heaptrans::complement_formula(formulat* f) {
  formulat* tmp = heaptrans::copy_formula(f);
 
  debugc("[complement_formula] : f = " << *f, 0);
  debugc("[complement_formula] : tmp = " << *tmp, 0);

  if(tmp->begin() != tmp->end()) {
    clauset* c = tmp->back();
    tmp->pop_back();
    formulat* lhs = heaptrans::complement_clause(c);

    debugc("[complement_formula]: lhs = " << *lhs, 0);
    formulat* compl_tmp = heaptrans::complement_formula(tmp);
    formulat* res = heaptrans::distribute_disj(lhs, compl_tmp);
    return res;
  }

  return f;
}

formulat* heaptrans::distribute_disj(formulat* f1, formulat* f2) {
  formulat* res = new formulat;

  debugc("[distribute_disj] : f1 = " << *f1, 0);
  debugc("[distribute_disj] : f2 = " << *f2, 0);

  if (f1->size() == 0)
    return f2;

  if (f2->size() == 0)
    return f1;

  for (formulat::const_iterator it1 = f1->begin(); it1 != f1->end(); ++it1)
    for (formulat::const_iterator it2 = f2->begin(); it2 != f2->end(); ++it2) {
      clauset* c = new clauset;
      c->insert(c->begin(), (*it2)->begin(), (*it2)->end());
      c->insert(c->begin(), (*it1)->begin(), (*it1)->end());
      res->push_back(c);
    }

  return res;
}

formula_ssat* heaptrans::process_conditional(formulat* cond, 
					    formula_ssat* c1ssa, 
					     formula_ssat* c2ssa) {
  ssa_countst* res = new ssa_countst;

  ssa_countst* ssa_count1 = c1ssa->second;
  ssa_countst* ssa_count2 = c2ssa->second;
  formulat* c1 = c1ssa->first;
  formulat* c2 = c2ssa->first;

  // complement the test condition
  debugc("[process_loop] : cond = " << *cond, 0);
  formulat* neg_cond = heaptrans::complement_formula(cond);

  c1->insert(c1->begin(), cond->begin(), cond->end());
  c2->insert(c2->begin(), neg_cond->begin(), neg_cond->end());
  debugc("[process_loop] : neg_cond = " << *neg_cond, 0);

  //ssa_count1 = heaptrans::ssa(c1);
  //ssa_count2 = heaptrans::ssa(c2);

  // add dummy equalities to reach the same ssa count on both branches
  // compare ssa counts of vars in c1 to those in c2
  for(ssa_countst::const_iterator it1 = ssa_count1->begin(); it1 != ssa_count1->end(); ++it1) {
    heapvar v1 = (*it1).first;
    int count1 = (*it1).second;
    debugc("[process_conditional]: v1 = " << v1 << " and count1 = " << count1, 0);
    for(ssa_countst::const_iterator it2 = ssa_count2->begin(); it2 != ssa_count2->end(); ++it2) {
      heapvar v2 = (*it2).first;
      int count2 = (*it2).second;
      debugc("[process_conditional]: v2 = " << v2 << " and count2 = " << count2, 0);
      if (v1.name.std::string::compare(v2.name) == 0) {
	if (count1 != count2) { 
	  std::stringstream ss1, ss2;
	  ss1 << v1.name << count1;
	  ss2 << v2.name << count2;
	  heapvar hv1 = heapvar(ss1.str());
	  heapvar hv2 = heapvar(ss2.str());
	  heaplitp newhl;
	  if(v1.name.std::string::compare("m") == 0)
	    // assuming that vars called "m" denote memory configurations
	    newhl = new mem_eq_lit(hv1, hv2, stateTrue);
	  else {
	    // pure = true; dummy = true;
	    newhl = new eq_lit(hv1, hv2, stateTrue, true, true);
	  }

	  if(count1 < count2) {
	    c1 = heaptrans::insert_lit_in_formula(newhl, c1);
	    res->push_back(*it2);
	  }
	  else {
	    c2 = heaptrans::insert_lit_in_formula(newhl, c2);
	    res->push_back(*it1);
	  }
	}
	else {
	  res->push_back(*it1);
	}
	break;
      }
    }
    if(it1 == ssa_count1->end())
      res->push_back(*it1);
  }

  // there may be vars that only appear in c2 
  // for themadd dummy equlities to c1
  for(ssa_countst::const_iterator it2 = ssa_count2->begin();
      it2 != ssa_count2->end();
      ++it2) {
      
    heapvar v2 = (*it2).first;

    for(ssa_countst::const_iterator it1 = ssa_count1->begin();
	it1 != ssa_count1->end();
	++it1) {
      heapvar v1 = (*it1).first;

      if (v1.name.std::string::compare(v2.name) == 0) {
	break;
      }
    }
    if(it2 == ssa_count2->end())
      res->push_back(*it2);
  }
      
  //ssa_count = res;

  // after SSA -> distribute
  formulat* f = heaptrans::distribute_disj(c1, c2);
  //formula.insert(formula.end(), f->begin(), f->end());
  debugc("[process_conditional] : ssa_count = " << *res, 0);
  return new formula_ssat(f, res);
}

  
std::vector<std::pair<heapvar, int> >* heaptrans::ssa_literal(heaplitp hl) {
  int count;
  std::set<heapvar> vars;
  ssa_countst* res = new ssa_countst;
  ssa_countst::iterator it1;
  debugc("[ssa_literal]: processing literal " << hl, 0);

  *res = *ssa_count;

  // first process unchanged vars
  // this is not going to increment the ssa counter
  vars = hl->get_rhs_vars();

  // here we also consider rhs mem vars
  std::set<heapvar> rhs_mem_vars = hl->get_rhs_mems();
  vars.insert(rhs_mem_vars.begin(), rhs_mem_vars.end());

  debugc("[ssa_literal]: rhs vars = " << vars, 0);

  for(std::set<heapvar>::iterator vit = vars.begin(); vit != vars.end(); ++vit) {
    // do not SSA NULL and *
    if(!vit->is_nil() && (*vit).name.std::string::compare("*") != 0) {
      debugc("[ssa_literal]: processing var RHS " << *vit, 0);      
	
      // search for the current ssa count
      for(it1 = res->begin(); it1 != res->end(); ++it1) {
	if((*vit).name.std::string::compare((*it1).first.name) == 0) {
	  debugc("[ssa_literal] : found " << (*it1).first, 0);
	  count = (*it1).second;
	  break;
	}
      }

      if(it1 == res->end()) {
	// introduce a new record with count 0 for the current variable
	count = 0;
	debugc("[ssa_literal] : reset count", 0);
	res->push_back(std::make_pair(*vit, count));
      }

      std::stringstream ss;
      ss << (*vit).name << count;
      hl->rename_vars_rhs((*vit).name, ss.str());
      hl->rename_rhs_mems((*vit).name, ss.str());
    }
  }

  // now process vars that are assigned
  std::set<heapvar> lhs_vars = hl->get_lhs_vars();

  // also consider lhs mem vars
  std::set<heapvar> lhs_mem_vars = hl->get_lhs_mems();
  lhs_vars.insert(lhs_mem_vars.begin(), lhs_mem_vars.end());

  debugc("[ssa_literal]: lhs vars = " << vars, 0);

  for(std::set<heapvar>::iterator vit = lhs_vars.begin(); vit != lhs_vars.end(); ++vit) {
    // do not SSA NULL and *
    if(!vit->is_nil() && (*vit).name.std::string::compare("*") != 0) {
      debugc("[ssa_literal]: processing var " << *vit, 0);      
	
      // search for the current ssa count
      for(it1 = res->begin(); it1 != res->end(); ++it1) {
	if((*vit).name.std::string::compare((*it1).first.name) == 0) {
	  debugc("[ssa_literal] : found " << (*it1).first, 0);
	  // increase the count
	  (*it1).second++;
	  count = (*it1).second;
	  break;
	}
      }

      if(it1 == res->end()) {
	// introduce a new record with count 0 for the current variable
	count = 0;
	debugc("[ssa_literal] : reset count", 0);
	res->push_back(std::make_pair(*vit, count));
      }

      std::stringstream ss;
      ss << (*vit).name << count;
      //x.name = ss.str();
      hl->rename_vars_lhs((*vit).name, ss.str());
      //(*vit).x = x;
      //count++;

      hl->rename_lhs_mems((*vit).name, ss.str());
    }
  }
  //      }
  return res;

}

ssa_countst* heaptrans::ssa(formulat* v) {

  ssa_countst::iterator it1;
  ssa_countst* res = new ssa_countst;
  ssa_countst* aux;

  *res = *ssa_count;
  for(formulat::const_iterator it1 = v->begin(); it1 != v->end(); ++it1) {
    for(clauset::const_iterator it2 = (*it1)->begin(); it2 != (*it1)->end(); ++it2) {
      ssa_count = ssa_literal(*it2);
    }
  }
  debugc("[ssa] : res = " << *ssa_count, 1);
  aux = ssa_count;
  ssa_count = res;
  res = aux;
  debugc("[ssa] : res = " << *res, 1);
  return res;
}
 
// return the set of memory vars in the formula
std::set<heapvar> heaptrans::get_mems() const {
  std::set<heapvar> ret, tmp;

  for(formulat::const_iterator it = heaptrans::formula.begin(); it != heaptrans::formula.end(); ++it) {
    for(clauset::const_iterator clause_it = (*it)->begin(); clause_it != (*it)->end(); ++clause_it) {
      tmp = (*clause_it)->get_mems();
      ret.insert(tmp.begin(), tmp.end());
    }
  }
  return ret;
}
  
// return the set of pointer vars in the formula
std::set<heapvar> heaptrans::get_vars() const {
  std::set<heapvar> ret, tmp;

  for(formulat::const_iterator it=heaptrans::formula.begin(); it!=heaptrans::formula.end(); ++it) {
    for(clauset::const_iterator clause_it = (*it)->begin(); clause_it != (*it)->end(); ++clause_it) {
      tmp = (*clause_it)->get_vars();
      ret.insert(tmp.begin(), tmp.end());
    }
  }
  return ret;
}

std::set<heapvar> heaptrans::get_vars_before(heaplit* lit) const {
  std::set<heapvar> ret, tmp;
  bool done = false;

  for(formulat::const_iterator it=heaptrans::formula.begin(); it!=heaptrans::formula.end() && !done; ++it) {
    for(clauset::const_iterator clause_it = (*it)->begin(); clause_it != (*it)->end() && !done; ++clause_it) {
      if(**clause_it == *lit) {
	debugc("[get_vars_before] : **clause_it == " << **clause_it, 1);
	done = true;
      }
      if (!(*clause_it)->dummy) {
	tmp = (*clause_it)->get_vars();
	ret.insert(tmp.begin(), tmp.end());
      }
    }
  }

  debugc("[get_vars_before] : ret = " << ret, 1);

  return ret;
}
  

formulat* heaptrans::insert_lit_in_formula(const heaplitp e, formulat* f) {
    
  clauset* newclause = new std::vector<heaplitp>();
  newclause->push_back(e);

  f->push_back(newclause);
  return f;
}

formulat* heaptrans::insert_clause_in_formula(formulat* f, clauset* c) {
  f->push_back(c);
  return f;
 
}

bool heaptrans::equal_clauses (const clauset* c1, const clauset* c2, heapabs& sol) {
  bool found = true;

  for(clauset::const_iterator it1 = c1->begin(); it1 != c1->end(); ++it1) {
    debugc("[equal_clauses]: checking lit = " << **it1, 0);
    if (!found) {
      debugc("[equal_clauses]: c1 = " << *c1 << " and c2 = " << *c2 << " with result false", 0);
      return false;
    }

    found = false;

    if((*it1)->type != STORE && (*it1)->type != MEMEQ && (*it1)->type != NEW && (*it1)->type != FREE) {
      // check if the literal is actually false
      meetIrreduciblep mi = copy_lit(**it1);
      entailResult::s insol = sol.entails(mi);

      if (insol == entailResult::False) {
	found = true;
	continue;
      }
    }

    for(clauset::const_iterator it2 = c2->begin(); it2 != c2->end(); ++it2) {
      if (**it1 == **it2) {
	debugc("[equal_clauses]: lit1 = " << **it1 << " and lit2 = " << **it2, 0);
	found  = true;
	break;
      }
    }
  }

  if (!found) {
    debugc("[equal_clauses]: c1 = " << *c1 << " and c2 = " << *c2 << " with result false", 0);
    return false;
  }
    
  debugc("[equal_clauses]: c1 = " << *c1 << " and c2 = " << *c2 << " with result true", 0);
  return true;
}


bool heaptrans::formula_contains_literal(const heaplitp hl, heapabs& sol) {
  // the literal must be unit clause
  bool ret =  false;
  clauset c;
  c.push_back(hl);

  for(formulat::const_iterator it = heaptrans::formula.begin(); it != heaptrans::formula.end(); ++it) {
    if (equal_clauses(&c, *it, sol) && equal_clauses(*it, &c, sol)) { 
      ret = true;
      break;
    }
  }
  debugc("[formula_contains_literal]: searching for hl = " << hl << " with result " << ret, 0);
  debugc("[formula_contains_literal]: formula = " << heaptrans::formula, 0);
  return ret;
}

// todo: normalize instead
bool heaptrans::single_literal(const clauset* c, const heaplitp l) const {
  // must be equal to all the disjuncts
  for(clauset::const_iterator lit_it = c->begin(); lit_it != c->end(); ++lit_it) {
    if (*lit_it != l)
      return false;
  }
  return true;
}

bool heaptrans::pure_literal(const heaplitp l) const {
  return l->type == PATH || l->type == ONPATH || l->type == DANGLING || l->type == EQ;
}
  
//add the pure literals in clause c as hints
void heaptrans::add_hints(const clauset* c, heapabs& sol) {
  debugc("[add_hints]: trying clause = " << *c, 0);
  debugc("[add_hints]: sol = " << sol.contents, 0);
  debugc("[add_hints]: formula = " << heaptrans::formula, 0);
  for(clauset::const_iterator it = c->begin(); it != c->end(); ++it) {
    heaplitp hl = *it;

    if (pure_literal(hl)) {
      debugc("[add_hints]: checking literal " << hl, 0);

      // check that the complemented literal is not in solution, hints, formula
      // in order not to add facts already known as hints
      meetIrreduciblep mi = copy_lit(*hl);

      if(hint_contains(mi))
	// already registered as a hint
	continue;

      mi->lit->complement();

      if(hint_contains(mi))
	// its negation is registered as a hint
	continue;

      entailResult::s insol = sol.entails(mi);
      bool informula = heaptrans::formula_contains_literal(mi->lit, sol);

      debugc("[add_hints]: hl = " << hl << " and informula = " << informula, 0);
      debugc("[add_hints]: hl = " << hl << " and insol = " << insol, 0);
      mi->lit->complement();

      // not in formula, solution, hint
      if (!informula && insol==entailResult::Incomplete) {
	hint.insert(std::make_pair(mi, hintPriority::High));
	debugc("[add_hints]: inserted hint " << mi, 1);
      }
      else {
	delete mi;
      }
    }
  }
  return;
}

bool heaptrans::unit_clause (const clauset* c, heaplitp& unit, heapabs& sol) {
  bool unitb = true;
  bool found;

  debugc("[unit_clause]: clause = " << *c, 1);

  for(unsigned int i = 0; i < c->size(); ++i) {
    // current literal
    heaplitp hl = (*c)[i];
    debugc("[unit_clause] : current hl = " << hl, 1);

    // search for the complement in both formula and current solution
    // as it could have been added to the solution as a decision
    if(hl->type != NEW && hl->type != STORE && hl->type != FREE && hl->type != MEMEQ) {
      meetIrreduciblep newl = copy_lit(*hl);
      debugc("[unit_clause] : literal currently processed = " << newl, 1);
      newl->complement();
      debugc("[unit_clause] : newl complemented = " << newl, 0);
    
      if(sol.entails(newl) != entailResult::True) {
	// did not find it in the current solution
	// search in formula
	found = false;

	debugc("[unit_clause] : searching in formula for newl = " << newl, 1);
	for(formulat::const_iterator it = heaptrans::formula.begin(); it != heaptrans::formula.end(); ++it) {
	  if (*it != c && heaptrans::single_literal(*it, newl->lit)) {
	    found = true;
	    break;
	  }
	}
      } 
      else {
	debugc("[unit_clause] : " << newl << " exists in the solution ", 1);
	debugc("[unit_clause] : sol.not_eqs = " << sol.not_eqs, 1);
	//debugc("[unit_clause] : equiv classes " << sol.equiv_sets, 1);
	found = true;
      }
      debugc("[unit_clause] : found = " << found, 0);
      //newl->complement();
      delete newl;

    }
    else {
      found = false;
    }

    if (!found || (i == c->size()-1 && unitb)) {
      if (unitb) {
	// set the literal believed to be unit clause
	unit = hl;
	debugc("[unit_clause] : possible unit clause " << unit, 1);
	// literal set
	unitb = false;
      }
      else {
	// not unit clause
	debugc("[unit_clause] : END", 1);

	// set it as a hint
	// meetIrreduciblep h = copy_lit(*unit);
	// sol.hint.insert(std::make_pair(h, hintPriority::High));
	// debugc("[add_hints]: inserted hint: " << h, 1);

	return false;
      }
    }
  }
  debugc("[unit_clause]: unit clause :) ", 1);
  return true;
}


clauset* heaptrans::simplify_clause (clauset* c, heapabs& sol) {
  bool unitb = true;
  bool found;
  unsigned int i;
  clauset* newc = new clauset;

  debugc("[simplify_clause]: clause = " << *c, 0);


  if(c->size() == 1) {
    return c;
  }

  for(i = 0; i < c->size(); ++i) {
    // current literal
    heaplitp hl = (*c)[i];

    if(hl->type == NEW || hl->type == STORE || hl->type == FREE || hl->type == MEMEQ) {
      //newc->push_back(hl);
      //break;
      newc->push_back(hl);
      continue;
    }

    meetIrreduciblep newl = copy_lit(*hl);

    newl->complement();
    debugc("[simplify_clause] : literal currently processed = " << newl, 0);      

    // check if the clause is true
    for(clauset::const_iterator it = c->begin(); it != c->end(); ++it) {
      if(*(newl->lit) == **it) {
	debugc("[simplify_clause] : clause is True (1) c = " << *c, 1);
	newc->clear();
	//delete newl;
	return newc;
      }
    }

    found = false;

    // search for the complement in the formula 
    for(formulat::const_iterator it = heaptrans::formula.begin(); it != heaptrans::formula.end(); ++it) {
      if(*it != c && heaptrans::single_literal(*it, newl->lit)) {
	debugc("[simplify_clause] : found literal (2) newl = " << newl, 1);
	found = true;
	break;
      }
    }

    // search for the complement in the solution as well
    if(!found && sol.entails(newl) != entailResult::True) {
      // cannot be removed
      newl->complement();
      newc->push_back(newl->lit);
    }

  }
  
  debugc("[simplify_clause] : newc = " << *newc << " and c = " << *c, 1);
  return newc;
}

void heaptrans::simplify_formula (heapabs& sol) {
  formulat f;

  for(formulat::iterator it = formula.begin(); it != formula.end(); ++it) {
    clauset* c = simplify_clause(*it, sol);
    if(!c->empty())
      f.push_back(c);
  }
  
  formula = f;

}

clauset* heaptrans::create_disjunction(std::vector< meetIrreduciblep >& v ) {
  clauset* clause = new clauset;
    
  for(std::vector< meetIrreduciblep >::const_iterator it = v.begin(); it != v.end(); ++it) {
    clause->push_back((*it)->lit);
  }

  return clause;
}

bool heaptrans::hint_contains(const meetIrreduciblep& e) const {
  hintt::const_iterator it;

  for(it = hint.begin(); it != hint.end(); ++it) {
    meetIrreducible_comp comp;

    if (!comp(it->first, e) && !comp(e, it->first)) {
      //debugc("[hint_contains] : found hint " << e, 1);
      return true;
    }
  }

  return false;
}


void heaptrans::clear () {
  for(formulat::const_iterator it=heaptrans::formula.begin(); it!=heaptrans::formula.end(); ++it) {
    (*it)->clear();
  }
  heaptrans::formula.clear();    
  heaptrans::watch.w.clear(); // todo: fix mem leak
}

void heaptrans::insert_literal(const heaplitp e) {
  clauset* newclause = new std::vector<heaplitp>();
  newclause->push_back(e);

  heaptrans::formula.push_back(newclause);
  heaptrans::watch.add_clause_to_watch(newclause);
}

void heaptrans::insert_clause(clauset* c) {
  heaptrans::formula.push_back(c);
 
  // add the clause to the watch lists of the first two literals
  heaptrans::watch.add_clause_to_watch(c);

}

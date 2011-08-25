/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string.h>

#include <set>
#include <fstream>

#include <simplify_expr.h>
#include <i2string.h>
#include <str_getline.h>
#include <bitvector.h>
#include <arith_tools.h>
#include <std_expr.h>

#include <langapi/language_util.h>

#include "slice_by_trace.h"

/*******************************************************************\

Function: slice_by_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slice_by_tracet::slice_by_trace(std::string trace_files,
					   symex_target_equationt &equation)
{
  std::cout << "Slicing by trace..." << std::endl;

  merge_identifier = "goto_symex::\\merge";
  merge_symbol=symbol_exprt(typet("bool"));
  merge_symbol.set_identifier(merge_identifier);

  std::vector<exprt> trace_conditions;

  size_t length = trace_files.length();
  for(size_t idx = 0; idx < length; idx++) {
    const std::string::size_type next = trace_files.find(",", idx);
    std::string filename = trace_files.substr(idx, next - idx);

    read_trace(filename);
    
    compute_ts_back(equation);
    
    exprt t_copy (t[0]);
    trace_conditions.push_back(t_copy);

    if(next == std::string::npos) break;
    idx = next;
  }
    
  exprt trace_condition;

  if (trace_conditions.size() == 1) {
    trace_condition = trace_conditions[0];
  } else {
    trace_condition = exprt("and",typet("bool"));
    trace_condition.operands().reserve(trace_conditions.size());
    for (std::vector<exprt>::iterator i = trace_conditions.begin();
	 i != trace_conditions.end(); i++) {
      trace_condition.move_to_operands(*i);
    }
  }

  simplify(trace_condition, ns);

  std::set<exprt> implications = implied_guards(trace_condition);
    
  for(std::set<exprt>::iterator i = sliced_guards.begin(); i !=
	sliced_guards.end(); i++)
  {
    exprt g_copy (*i);

    if (g_copy.id() == "symbol" || g_copy.id() == "not")
    {
      g_copy.make_not();
      simplify(g_copy, ns);
      implications.insert(g_copy);
    }
    else if (g_copy.id() == "and")
    {
      exprt copy_last (g_copy.operands().back());
      copy_last.make_not();
      simplify(copy_last, ns);
      implications.insert(copy_last);
    }
    else if (!(g_copy.id() == "constant")) {
      throw "Guards should only be and, symbol, constant, or not.";
    }
  }
 
  slice_SSA_steps(equation, implications); // Slice based on implications

  guardt t_guard;
  t_guard.make_true();
  symex_targett::sourcet empty_source;
  equation.SSA_steps.push_front(symex_target_equationt::SSA_stept());
  symex_target_equationt::SSA_stept &SSA_step = equation.SSA_steps.front(); 

  SSA_step.guard_expr=t_guard.as_expr();
  SSA_step.ssa_lhs.make_nil();
  SSA_step.cond_expr.swap(trace_condition);
  SSA_step.type=goto_trace_stept::ASSUME;
  SSA_step.source=empty_source;

  assign_merges(equation); // Now add the merge variable assignments to eqn
  
  std::cout << "Finished slicing by trace..." << std::endl;
}

/*******************************************************************\

Function: read_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slice_by_tracet::read_trace(std::string filename)
{
  std::cout << "Reading trace from file " << filename << std::endl;
  std::ifstream file(filename.c_str());
  if (file.fail())
    throw "Failed to read from trace file.";

  // In case not the first trace read
  alphabet.clear();
  sigma.clear(); 
  sigma_vals.clear();
  t.clear();
  
  std::string read_line;
  bool done = false;
  bool begin = true;
  alphabet_parity = true;
  
  while (!done && !file.eof ()) {
    str_getline(file, read_line);
    if (begin && (read_line == "!"))
      alphabet_parity = false;
    else
      done = parse_alphabet(read_line);
  }
  
  while (!file.eof ()) {
    str_getline(file,read_line);
    parse_events(read_line);
  }
  
  for (size_t i = 0; i < sigma.size(); i++) {
    exprt f_e = static_cast<const exprt &>(get_nil_irep());
    f_e.make_false();
    t.push_back(f_e);
  }
    
  exprt t_e = static_cast<const exprt &>(get_nil_irep());
  t_e.make_true();
  t.push_back(t_e);
}  

/*******************************************************************\

Function: parse_alphabet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_slice_by_tracet::parse_alphabet(std::string read_line) {
  if ((read_line == ":") || (read_line == ":exact") || 
      (read_line == ":suffix") || (read_line == ":exact-suffix") ||
      (read_line == ":prefix")) {
    semantics = read_line;
    return true;
  } else {
    std::cout << "Alphabet: ";
    if (!alphabet_parity) 
      std::cout << "!";
    std::cout << read_line << std::endl;
    alphabet.insert(read_line);
  }
  return false;
}

/*******************************************************************\

Function: parse_events

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slice_by_tracet::parse_events(std::string read_line) {
  if (read_line == "")
    return;
  bool parity = strstr(read_line.c_str(),"!")==NULL;
  bool universe = strstr(read_line.c_str(),"?")!=NULL;
  bool has_values = strstr(read_line.c_str()," ")!=NULL;
  std::cout << "Trace: " << read_line << std::endl;
  std::vector<irep_idt> value_v;
  if (has_values) {
    std::string::size_type sloc = read_line.find(" ",0);
    std::string values = (read_line.substr(sloc, read_line.size()-1));
    size_t length = values.length();
    for(size_t idx = 0; idx < length; idx++) {
      const std::string::size_type next = values.find(",", idx);
      std::string value = values.substr(idx, next - idx);
      value_v.push_back(value);
      if(next == std::string::npos) break;
      idx = next;
    }
    read_line = read_line.substr(0,sloc);
  }
  sigma_vals.push_back(value_v);
  if (universe)
    parity = false;
  if (!parity) 
    read_line = read_line.substr(1,read_line.size()-1);
  std::set<irep_idt> eis;
  size_t vlength = read_line.length();
  for(size_t vidx = 0; vidx < vlength; vidx++) {
    const std::string::size_type vnext = read_line.find(",", vidx);
    std::string event = read_line.substr(vidx, vnext - vidx);
    eis.insert(event);
    if ((!alphabet.empty()) && ((alphabet.count(event) != 0) != 
				alphabet_parity))
      throw ("Trace uses symbol not in alphabet: " + event);
    if(vnext == std::string::npos) break;
    vidx = vnext;
  }
  event_sett es = event_sett(eis, parity);
  sigma.push_back(es);
}

/*******************************************************************\

Function: compute_ts_back

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slice_by_tracet::compute_ts_back(
  symex_target_equationt &equation)
{
  size_t merge_count = 0;

  for(symex_target_equationt::SSA_stepst::reverse_iterator
      i=equation.SSA_steps.rbegin();
      i!=equation.SSA_steps.rend(); 
      i++)
  {
    if(i->is_output() &&
       !i->io_args.empty() &&
       i->io_args.front().id()=="trace_event")
    {
      irep_idt event = i->io_args.front().get("event");
      
      if (!alphabet.empty())
      {
	bool present = (alphabet.count(event) != 0);
	if (alphabet_parity != present)
	  continue;
      }
      
      exprt guard = i->guard_expr;

#if 0
      std::cout << "EVENT:  " << event << std::endl;
      std::cout << "GUARD:  " << from_expr(ns, "", guard) << std::endl;
      for (size_t j = 0; j < t.size(); j++) {
        std::cout << "t[" << j << "] = " << from_expr(ns, "", t[j]) <<
          std::endl;
      }
#endif

      bool slice_this = (semantics != ":prefix");
      std::vector<exprt> merge;
      
      for(size_t j = 0; j < t.size(); j++) {
	if ((t[j].is_true()) || (t[j].is_false())) {
	  merge.push_back(t[j]);
	} else {
	  exprt merge_sym =exprt("symbol", typet("bool"));
	  merge_sym.set("identifier", id2string(merge_identifier)+"#"+
			i2string(merge_count++));
	  exprt t_copy (t[j]);
	  merge_map_back.push_back(t_copy);
	  std::set<exprt> empty_impls;
	  merge_impl_cache_back.push_back
	    (std::pair<bool,std::set<exprt> >(false, empty_impls));
	  merge.push_back(merge_sym);
	}
      }

      for(size_t j = 0; j < t.size(); j++) {
	exprt u_lhs = exprt("and", typet("bool"));
	if ((j < sigma.size()) && (matches(sigma[j],event))) {
	  u_lhs.operands().reserve(2);
	  u_lhs.copy_to_operands(guard);
	  if (!sigma_vals[j].empty()) {
	    std::list<exprt> eq_conds;
	    std::list<exprt>::iterator pvi = i->io_args.begin();
	    for (std::vector<irep_idt>::iterator k = sigma_vals[j].begin();
		 k != sigma_vals[j].end(); k++) {
	      
	      exprt equal_cond=exprt("=", typet("bool"));
	      equal_cond.operands().reserve(2);
	      equal_cond.copy_to_operands(*pvi);
	      // Should eventually change to handle non-bv types!
	      exprt constant_value = exprt("constant",(*pvi).type());
	      std::string bit_string = 
		integer2binary(atoi(k->c_str()), bv_width((*pvi).type()));
	      constant_value.set("value", bit_string);
	      equal_cond.move_to_operands(constant_value);
	      eq_conds.push_back(equal_cond);
	      pvi++;
	    }
	    exprt val_merge = exprt("and", typet("bool"));
	    val_merge.operands().reserve(eq_conds.size()+1);
	    val_merge.copy_to_operands(merge[j+1]);
	    for (std::list<exprt>::iterator k = eq_conds.begin(); 
		 k!= eq_conds.end(); k++) {
	      val_merge.copy_to_operands(*k);
	    }
	    u_lhs.move_to_operands(val_merge);
	  } else {
	    u_lhs.copy_to_operands(merge[j+1]);
	  }

	  simplify(u_lhs, ns);
	  
	  if ((!u_lhs.is_false()) && implies_false(u_lhs))
	    u_lhs.make_false();
	  if (!u_lhs.is_false())
	    slice_this = false;
	} else {
	  u_lhs.make_false();
	}
	exprt u_rhs = exprt ("and", typet("bool"));
	if ((semantics != ":suffix") || (j != 0)) {
	  u_rhs.operands().reserve(2);
	  u_rhs.copy_to_operands(guard);
	  u_rhs.copy_to_operands(merge[j]);
	  u_rhs.op0().make_not();
	} else {
	  u_rhs.swap(merge[j]);
	}
	exprt u_j = exprt ("or", typet("bool"));
	u_j.operands().reserve(2);
	u_j.copy_to_operands(u_lhs);
	u_j.copy_to_operands(u_rhs);

	simplify(u_j, ns);

	t[j] = u_j;
      }
      
      if (semantics == ":prefix")
	t[t.size()-1].make_true();
      
      if (slice_this) {
	exprt guard_copy(guard);
	
	sliced_guards.insert(guard_copy);
      }
    }
  }
}

/*******************************************************************\

Function: compute_ts_fd

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slice_by_tracet::compute_ts_fd(
  symex_target_equationt &equation)
{
}

/*******************************************************************\

Function:  slice_SSA_steps

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slice_by_tracet::slice_SSA_steps(
  symex_target_equationt &equation, 
  std::set<exprt> implications)
{
  //Some statistics for our benefit.
  size_t conds_seen = 0;
  size_t sliced_SSA_steps = 0;
  size_t potential_SSA_steps = 0;
  size_t sliced_conds = 0;
  size_t trace_SSA_steps = 0;
  size_t location_SSA_steps = 0;
  size_t trace_loc_sliced = 0;

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    if (it->is_output())
      trace_SSA_steps++;
    if (it->is_location())
      location_SSA_steps++;
    bool sliced_SSA_step = false;
    exprt guard=it->guard_expr;

    simplify(guard, ns);

    if (!guard.is_true())
      potential_SSA_steps++;
    //it->output(ns,std::cout);
    //std::cout << "-----------------" << std::endl;

    if ((guard.id() == "symbol") || (guard.id() == "not"))
    {
      guard.make_not();
      simplify(guard, ns);
      
      if (implications.count(guard) != 0) {
	it->cond_expr.make_true();
	it->ssa_rhs.make_true();
	it->guard_expr.make_false();
	sliced_SSA_steps++;
	if (it->is_output() || it->is_location())
	  trace_loc_sliced++;
	sliced_SSA_step = true;
      }
    }
    else if(guard.id()=="and")
    {
      Forall_operands(git,guard)
      {
	exprt neg_expr=*git;
	neg_expr.make_not();
	simplify(neg_expr, ns);
	
	if (implications.count(neg_expr) != 0) {
	  it->cond_expr.make_true();
	  it->ssa_rhs.make_true();
	  it->guard_expr.make_false();
	  sliced_SSA_steps++;
	  if (it->is_output() || it->is_location())
	    trace_loc_sliced++;
	  sliced_SSA_step = true;
	  break; // Sliced, so no need to consider the rest
	}
      } else if (guard.id() == "or") {
	std::cout << "Guarded by an OR." << std::endl;
      }
    }

    if(!sliced_SSA_step && it->is_assignment())
    {
      if(it->ssa_rhs.id()==ID_if)
      {
	conds_seen++;
	exprt cond_copy (it->ssa_rhs.op0());
	simplify(cond_copy, ns);
	
	if (implications.count(cond_copy) != 0) {
	  sliced_conds++;
	  exprt t_copy1 (it->ssa_rhs.op1());
	  exprt t_copy2 (it->ssa_rhs.op1());
	  it->ssa_rhs = t_copy1;
	  it->cond_expr.op1().swap(t_copy2);
	}
	else
	{
	  cond_copy.make_not();
	  simplify(cond_copy, ns);
	  if (implications.count(cond_copy) != 0) {
	    sliced_conds++;
	    exprt f_copy1 (it->ssa_rhs.op2());
	    exprt f_copy2 (it->ssa_rhs.op2());
	    it->ssa_rhs = f_copy1;
	    it->cond_expr.op1().swap(f_copy2);
	  }
	}
      }
    }
  }

  std::cout << "Trace slicing effectively removed " 
	    << (sliced_SSA_steps + sliced_conds) << " out of "
	    << equation.SSA_steps.size() << " SSA_steps." << std::endl;
  std::cout << "  (" 
    	    << ((sliced_SSA_steps + sliced_conds) - trace_loc_sliced) 
	    << " out of " 
	    << (equation.SSA_steps.size() - trace_SSA_steps - location_SSA_steps)
	    << " non-trace, non-location SSA_steps)" << std::endl;
}

/*******************************************************************\

Function:  matches

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_slice_by_tracet::matches(
  event_sett s,
  irep_idt event)
{
  bool present = s.first.count(event) != 0;
  return ((s.second && present) || (!s.second && !present));
}

/*******************************************************************\

Function:  assign_merges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slice_by_tracet::assign_merges(
  symex_target_equationt &equation)
{
  size_t merge_count = (merge_map_back.size()) - 1;
  for (std::vector<exprt>::reverse_iterator i = merge_map_back.rbegin();
       i != merge_map_back.rend(); i++) {
    symbol_exprt merge_sym(typet("bool"));
    merge_sym.set_identifier(id2string(merge_identifier)+"#"+i2string(merge_count));
    merge_count--;
    guardt t_guard;
    t_guard.make_true();
    symex_targett::sourcet empty_source;

    exprt merge_copy(*i);

    equation.SSA_steps.push_front(symex_target_equationt::SSA_stept());
    symex_target_equationt::SSA_stept &SSA_step = equation.SSA_steps.front();  
    
    SSA_step.guard_expr=t_guard.as_expr();
    SSA_step.ssa_lhs=merge_sym;
    SSA_step.original_lhs_object=merge_symbol;
    SSA_step.ssa_rhs.swap(merge_copy);
    SSA_step.assignment_type=symex_targett::HIDDEN;
    
    SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_rhs);
    SSA_step.type=goto_trace_stept::ASSIGNMENT;
    SSA_step.source=empty_source;
  }
}

/*******************************************************************\

Function:  implied_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> symex_slice_by_tracet::implied_guards(exprt e)
{
  std::set<exprt> s;

  if (e.id() == "symbol") { // Guard or merge
    const char* merge_loc = strstr(e.get("identifier").c_str(),"merge#");
    if (merge_loc == NULL) {
      exprt e_copy (e);
      simplify(e_copy, ns);
      s.insert(e_copy);
      return s;
    } else {
      int i = atoi(merge_loc+1);
      if (merge_impl_cache_back[i].first) {
	return merge_impl_cache_back[i].second;
      } else {
	merge_impl_cache_back[i].first = true;
	exprt merge_copy (merge_map_back[i]);
	merge_impl_cache_back[i].second = implied_guards(merge_copy);
	return merge_impl_cache_back[i].second;
      }
    }
  } else if (e.id() == "not") { // Definitely a guard
    exprt e_copy(e);
    simplify(e_copy, ns);
    s.insert(e_copy);
    return s;
  } else if (e.id() == "and") { // Descend into and
    Forall_operands(it,e) {
      std::set<exprt> r = implied_guards(*it);
      for (std::set<exprt>::iterator i = r.begin();
	   i != r.end(); i++) {
	s.insert(*i);
      }
    }
    return s;
  } else if (e.id() == "or") { // Descend into or
    std::vector<std::set<exprt> > rs;
    Forall_operands(it,e) {
      rs.push_back(implied_guards(*it));
    }
    for (std::set<exprt>::iterator i = rs.front().begin();
	 i != rs.front().end();) {
      for (std::vector<std::set<exprt> >::iterator j = rs.begin();
	 j != rs.end(); j++) {
	if (j == rs.begin())
	  j++;
	std::set<exprt>::iterator k = i;
	i++;
	if (j->count(*k) == 0) {
	  rs.front().erase(k);
	  break;
	}
      }
    }
    s = rs.front();
    return s;
  }

  return s;
}

/*******************************************************************\

Function: symex_slice_by_tracet::implies_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_slice_by_tracet::implies_false(const exprt e)
{
  std::set<exprt> imps = implied_guards(e);

  for(std::set<exprt>::iterator
      i=imps.begin();
      i!=imps.end(); i++)
  {
    exprt i_copy (*i);
    i_copy.make_not();
    simplify(i_copy, ns);
    if (imps.count(i_copy) != 0)
      return true;
  }

  return false;
}

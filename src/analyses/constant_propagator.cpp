/*******************************************************************\

Module: Constant Propagation

Author: Peter Schrammel

\*******************************************************************/

//#define DEBUG

#include <iostream>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>

#include "constant_propagator.h"

/*******************************************************************\

Function: const_propagator_domaint::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_propagator_domaint::assign_rec(
  valuest &values,
  const exprt &lhs, const exprt &rhs,
  const namespacet &ns)
{
  const typet & rhs_type = ns.follow(rhs.type());

#ifdef DEBUG
  std::cout << "assign: " << from_expr(ns, "", lhs)
	    << " := " << from_type(ns, "", rhs_type) << std::endl;
#endif

  if(lhs.id()==ID_symbol && rhs_type.id()!=ID_array
                         && rhs_type.id()!=ID_struct
                         && rhs_type.id()!=ID_union)
  {
    if(!values.maps_to_top(rhs))
      assign(values,lhs,rhs,ns);
    else
      values.set_to_top(lhs);
  }
#if 0
  else //TODO: could make field or array element-sensitive
  {
  }
#endif
}

/*******************************************************************\

Function: const_propagator_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_propagator_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
#ifdef DEBUG
  std::cout << from->location_number << " --> "
	    << to->location_number << std::endl;
#endif
  
  if(from->is_decl())
  {
    values.set_to_top(to_code_decl(from->code).symbol());
  }
  else if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    const exprt &lhs = assignment.lhs();
    const exprt &rhs = assignment.rhs();
    assign_rec(values,lhs,rhs,ns);
  }
  else if(from->is_goto())
  {
    if(from->guard.id()==ID_equal && from->get_target()==to)
    {
      const exprt &lhs = from->guard.op0(); 
      const exprt &rhs = from->guard.op1();

      //two-way propagation 
      valuest copy_values = values;
      assign_rec(copy_values,lhs,rhs,ns);
      assign_rec(values,rhs,lhs,ns);
      values.merge(copy_values);
    }
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    values.set_to_top(code_dead.symbol());
  }
  else if(from->is_function_call())
  {
    values.set_all_to_top();
  }

#ifdef DEBUG
  output(std::cout,ai,ns);
#endif
}

/*******************************************************************\

Function: const_propagator_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_propagator_domaint::assign(
  valuest &dest,
  const exprt &lhs,
  exprt rhs,
  const namespacet &ns) const
{
#ifdef DEBUG
  std::cout << "assign:     " << from_expr(ns, "", lhs)
	    << " := " << from_expr(ns, "", rhs) << std::endl;
#endif

  values.replace_const(rhs);

#ifdef DEBUG
  std::cout << "replaced:   " << from_expr(ns, "", lhs)
	    << " := " << from_expr(ns, "", rhs) << std::endl;
#endif

  rhs = simplify_expr(rhs, ns);

#ifdef DEBUG
  std::cout << "simplified: " << from_expr(ns, "", lhs)
	    << " := " << from_expr(ns, "", rhs) << std::endl;
#endif

  dest.set_to(lhs,rhs);
}

/*******************************************************************\

Function: const_propagator_domaint::valuest::maps_to_top

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool const_propagator_domaint::valuest::maps_to_top(const exprt &expr) const
{
  if(expr.id()==ID_side_effect && 
     to_side_effect_expr(expr).get_statement()==ID_nondet) 
    return true;
  if(expr.id()==ID_symbol)
    if(replace_const.expr_map.find(expr.get(ID_identifier))
        == replace_const.expr_map.end())
      return true;
  forall_operands(it,expr)
  {
    if(maps_to_top(*it))
      return true;
  }
  return false;
}

/*******************************************************************\

Function: const_propagator_domaint::valuest::set_to_top

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool const_propagator_domaint::valuest::set_to_top(const irep_idt &id)
{
  bool result = false;
  replace_symbolt::expr_mapt::iterator r_it =
    replace_const.expr_map.find(id);
  if(r_it != replace_const.expr_map.end())
  {
    replace_const.expr_map.erase(r_it);
    result = true;
  }
  if(top_ids.find(id)==top_ids.end())
  {
    top_ids.insert(id);
    result = true;
  }
  return result;
}

bool const_propagator_domaint::valuest::set_to_top(const exprt &expr)
{
  return set_to_top(to_symbol_expr(expr).get_identifier());
}

void const_propagator_domaint::valuest::set_all_to_top()
{
  for(replace_symbolt::expr_mapt::iterator it =
        replace_const.expr_map.begin();
      it != replace_const.expr_map.end(); ++it)
    top_ids.insert(it->first);
  replace_const.expr_map.clear();
}


/*******************************************************************\

Function: const_propagator_domaint::valuest::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_propagator_domaint::valuest::set_to(const irep_idt &lhs_id,
					    const exprt &rhs_val)
{
  replace_const.expr_map[lhs_id] = rhs_val;
  std::set<irep_idt>::iterator it = top_ids.find(lhs_id);
  if(it!=top_ids.end()) top_ids.erase(it);
}

void const_propagator_domaint::valuest::set_to(const exprt &lhs,
					    const exprt &rhs_val)
{
  const irep_idt &lhs_id = to_symbol_expr(lhs).get_identifier();
  set_to(lhs_id,rhs_val);
}

/*******************************************************************\

Function: const_propagator_domaint::valuest::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_propagator_domaint::valuest::output(
  std::ostream &out,
  const namespacet &ns) const
{
  out << "const map: " << std::endl;
  for(replace_symbolt::expr_mapt::const_iterator 
	it=replace_const.expr_map.begin();
      it!=replace_const.expr_map.end();
      ++it)
    out << ' ' << it->first << "=" <<
      from_expr(ns, "", it->second) << std::endl;
  out << "top ids: " << std::endl;
  for(std::set<irep_idt>::const_iterator 
	it=top_ids.begin();
      it!=top_ids.end();
      ++it)
    out << ' ' << *it << std::endl;
}

/*******************************************************************\

Function: const_propagator_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_propagator_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  values.output(out,ns);
}

/*******************************************************************\

Function: const_propagator_domaint::valuest::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool const_propagator_domaint::valuest::merge(const valuest &src)
{
  bool changed = false;
  for(replace_symbolt::expr_mapt::const_iterator 
	it=src.replace_const.expr_map.begin();
      it!=src.replace_const.expr_map.end(); ++it)
  {
    replace_symbolt::expr_mapt::iterator 
      c_it = replace_const.expr_map.find(it->first);
    if(c_it != replace_const.expr_map.end())
    {
      if(c_it->second != it->second)
      {
        set_to_top(it->first);
	changed = true;
      }
    }
    else if(top_ids.find(it->first)==top_ids.end())
    {
      set_to(it->first,it->second);
      changed = true;
    }
  }
  for(std::set<irep_idt>::const_iterator it=src.top_ids.begin();
      it!=src.top_ids.end(); ++it)
  {
    bool c = set_to_top(*it);
    changed = changed || c;
  }

  return changed;
}

/*******************************************************************\

Function: const_propagator_domaint::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool const_propagator_domaint::merge(
  const const_propagator_domaint &other,
  locationt from,
  locationt to)
{
  return values.merge(other.values);
}

/*******************************************************************\

Function: const_propagator_ait::replace

  Inputs:

 Outputs: 

 Purpose:

\*******************************************************************/

void const_propagator_ait::replace(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  Forall_goto_program_instructions(it, goto_function.body)
  {
    state_mapt::iterator s_it = state_map.find(it);
    if(s_it == state_map.end())
      continue;
    replace_types_rec(s_it->second.values.replace_const, it->code);
    replace_types_rec(s_it->second.values.replace_const, it->guard);
    if(it->is_goto() || it->is_assume() || it->is_assert())
    {
      s_it->second.values.replace_const(it->guard);
      it->guard = simplify_expr(it->guard,ns);
    }
    else if(it->is_assign())
    {
      exprt &rhs = to_code_assign(it->code).rhs();
      s_it->second.values.replace_const(rhs);
      rhs = simplify_expr(rhs,ns);
    }
    else if(it->is_function_call())
    {
      exprt::operandst &args = 
	to_code_function_call(it->code).arguments();
      for(exprt::operandst::iterator o_it = args.begin();
	  o_it != args.end(); ++o_it)
      {
        s_it->second.values.replace_const(*o_it);
	*o_it = simplify_expr(*o_it,ns);
      }
    }
  }
}

/*******************************************************************\

Function: const_propagator_ait::replace_types_rec

  Inputs:

 Outputs: 

 Purpose:

\*******************************************************************/

void const_propagator_ait::replace_types_rec(
  const replace_symbolt &replace_const, 
  exprt &expr)
{
  replace_const(expr.type());
  Forall_operands(it,expr)
    replace_types_rec(replace_const,*it);
}


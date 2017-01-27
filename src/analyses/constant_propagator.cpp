/*******************************************************************\

Module: Constant Propagation

Author: Peter Schrammel

\*******************************************************************/

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>

#include "constant_propagator.h"

/*******************************************************************\

Function: constant_propagator_domaint::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_domaint::assign_rec(
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
    if(values.is_constant(rhs))
      assign(values, to_symbol_expr(lhs), rhs, ns);
    else
      values.set_to_top(to_symbol_expr(lhs));
  }
#if 0
  else // TODO: could make field or array element-sensitive
  {
  }
#endif
}

/*******************************************************************\

Function: constant_propagator_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  #ifdef DEBUG
  std::cout << from->location_number << " --> "
            << to->location_number << '\n';
  #endif

#ifdef DEBUG
  std::cout << "before:\n";
  output(std::cout, ai, ns);
#endif

  if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    const symbol_exprt &symbol=to_symbol_expr(code_decl.symbol());
    values.set_to_top(symbol);
  }
  else if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    const exprt &lhs = assignment.lhs();
    const exprt &rhs = assignment.rhs();
    assign_rec(values, lhs, rhs, ns);
  }
  else if(from->is_assume())
  {
    two_way_propagate_rec(from->guard, ns);
  }
  else if(from->is_goto())
  {
    exprt g;
    if(from->get_target()==to)
      g = simplify_expr(from->guard, ns);
    else
      g = simplify_expr(not_exprt(from->guard), ns);

    two_way_propagate_rec(g, ns);
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    values.set_to_top(to_symbol_expr(code_dead.symbol()));
  }
  else if(from->is_function_call())
  {
    const exprt &function=to_code_function_call(from->code).function();

    if(function.id()==ID_symbol)
    {
      const irep_idt &identifier=to_symbol_expr(function).get_identifier();

      if(identifier=="__CPROVER_set_must" ||
         identifier=="__CPROVER_get_must" ||
         identifier=="__CPROVER_set_may" ||
         identifier=="__CPROVER_get_may" ||
         identifier=="__CPROVER_cleanup" ||
         identifier=="__CPROVER_clear_may" ||
         identifier=="__CPROVER_clear_must")
      {
      }
      else
        values.set_to_top();
    }
    else
      values.set_to_top();
  }
#ifdef DEBUG
  std::cout << "after:\n";
  output(std::cout, ai, ns);
#endif
}


/*******************************************************************\

Function: constant_propagator_domaint::two_way_propagate_rec

  Inputs:

 Outputs:

 Purpose: handles equalities and conjunctions containing equalities

\*******************************************************************/

bool constant_propagator_domaint::two_way_propagate_rec(
  const exprt &expr,
  const namespacet &ns)
{
#ifdef DEBUG
  std::cout << "two_way_propagate_rec: " << from_expr(ns, "", expr) << '\n';
#endif
  bool change = false;

  if(expr.id()==ID_and)
  {
    // need a fixed point here to get the most out of it
    do
    {
      change = false;

      forall_operands(it, expr)
        if(two_way_propagate_rec(*it, ns))
          change = true;
    }
    while(change);
  }
  else if(expr.id()==ID_equal)
  {
    const exprt &lhs = expr.op0();
    const exprt &rhs = expr.op1();

    // two-way propagation
    valuest copy_values = values;
    assign_rec(copy_values, lhs, rhs, ns);
    if(!values.is_constant(rhs) || values.is_constant(lhs))
      assign_rec(values, rhs, lhs, ns);
    change = values.meet(copy_values);
  }

#ifdef DEBUG
  std::cout << "two_way_propagate_rec: " << change << '\n';
#endif
  return change;
}

/*******************************************************************\

Function: constant_propagator_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_domaint::assign(
  valuest &dest,
  const symbol_exprt &lhs,
  exprt rhs,
  const namespacet &ns) const
{
  values.replace_const(rhs);
  rhs = simplify_expr(rhs, ns);
  dest.set_to(lhs, rhs);
}

/*******************************************************************\

Function: constant_propagator_domaint::valuest::is_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool constant_propagator_domaint::valuest::is_constant(const exprt &expr) const
{
  if(expr.id()==ID_side_effect &&
     to_side_effect_expr(expr).get_statement()==ID_nondet)
    return false;

  if(expr.id()==ID_side_effect &&
     to_side_effect_expr(expr).get_statement()==ID_malloc)
    return false;

  if(expr.id()==ID_symbol)
    if(replace_const.expr_map.find(to_symbol_expr(expr).get_identifier()) ==
       replace_const.expr_map.end())
      return false;

  if(expr.id()==ID_address_of)
    return is_constant_address_of(to_address_of_expr(expr).object());

  forall_operands(it, expr)
    if(!is_constant(*it))
      return false;

  return true;
}

/*******************************************************************\

Function: constant_propagator_domaint::valuest::is_constant_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool constant_propagator_domaint::valuest::is_constant_address_of(
  const exprt &expr) const
{
  if(expr.id()==ID_index)
    return is_constant_address_of(to_index_expr(expr).array()) &&
           is_constant(to_index_expr(expr).index());

  if(expr.id()==ID_member)
    return is_constant_address_of(to_member_expr(expr).struct_op());

  if(expr.id()==ID_dereference)
    return is_constant(to_dereference_expr(expr).pointer());

  if(expr.id()==ID_string_constant)
    return true;

  return true;
}

/*******************************************************************\

Function: constant_propagator_domaint::valuest::set_to_top

  Inputs:

 Outputs:

 Purpose: Do not call this when iterating over replace_const.expr_map!

\*******************************************************************/

bool constant_propagator_domaint::valuest::set_to_top(const irep_idt &id)
{
  bool result = false;

  replace_symbolt::expr_mapt::iterator r_it =
    replace_const.expr_map.find(id);

  if(r_it != replace_const.expr_map.end())
  {
    assert(!is_bottom);
    replace_const.expr_map.erase(r_it);
    result = true;
  }

  return result;
}

/*******************************************************************\

Function: constant_propagator_domaint::valuest::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_domaint::valuest::output(
  std::ostream &out,
  const namespacet &ns) const
{
  out << "const map:\n";

  if(is_bottom)
    out << "  bottom\n";

  for(const auto &replace_pair : replace_const.expr_map)
    out << ' ' << replace_pair.first << "="
        << from_expr(ns, "", replace_pair.second) << '\n';
}

/*******************************************************************\

Function: constant_propagator_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  values.output(out, ns);
}

/*******************************************************************\

Function: constant_propagator_domaint::valuest::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose: join

\*******************************************************************/

bool constant_propagator_domaint::valuest::merge(const valuest &src)
{
  // nothing to do
  if(src.is_bottom)
    return false;

  // just copy
  if(is_bottom)
  {
    replace_const = src.replace_const;
    is_bottom = src.is_bottom;
    return true;
  }

  bool changed = false;

  // set everything to top that is not in src
  for(replace_symbolt::expr_mapt::const_iterator
        it=replace_const.expr_map.begin();
      it!=replace_const.expr_map.end();
      ) // no it++
  {
    if(src.replace_const.expr_map.find(it->first) ==
       src.replace_const.expr_map.end())
    {
      // cannot use set_to_top here
      replace_const.expr_map.erase(it++);
      changed = true;
    }
    else ++it;
  }

  for(const auto &src_replace_pair : src.replace_const.expr_map)
  {
    replace_symbolt::expr_mapt::iterator c_it=
      replace_const.expr_map.find(src_replace_pair.first);

    if(c_it!=replace_const.expr_map.end())
    {
      // values are different, set to top
      if(c_it->second!=src_replace_pair.second)
      {
        changed=set_to_top(src_replace_pair.first);
        assert(changed);
      }
    }
    // is not in "this", ignore
    else { }
  }

#ifdef DEBUG
  std::cout << "merged: " << changed << '\n';
#endif

  return changed;
}

/*******************************************************************\

Function: constant_propagator_domaint::valuest::meet

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose: meet

\*******************************************************************/

bool constant_propagator_domaint::valuest::meet(const valuest &src)
{
  if(src.is_bottom || is_bottom)
    return false;

  bool changed = false;

  for(const auto &src_replace_pair : src.replace_const.expr_map)
  {
    replace_symbolt::expr_mapt::iterator c_it=
      replace_const.expr_map.find(src_replace_pair.first);

    if(c_it!=replace_const.expr_map.end())
    {
      if(c_it->second!=src_replace_pair.second)
      {
        set_to_bottom();
        changed=true;
        break;
      }
    }
    else
    {
      set_to(src_replace_pair.first, src_replace_pair.second);
      changed=true;
    }
  }

  return changed;
}

/*******************************************************************\

Function: constant_propagator_domaint::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool constant_propagator_domaint::merge(
  const constant_propagator_domaint &other,
  locationt from,
  locationt to)
{
  return values.merge(other.values);
}

/*******************************************************************\

Function: constant_propagator_ait::replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_ait::replace(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  Forall_goto_functions(f_it, goto_functions)
    replace(f_it->second, ns);
}

/*******************************************************************\

Function: constant_propagator_ait::replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_ait::replace(
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
      it->guard = simplify_expr(it->guard, ns);
    }
    else if(it->is_assign())
    {
      exprt &rhs = to_code_assign(it->code).rhs();
      s_it->second.values.replace_const(rhs);
      rhs = simplify_expr(rhs, ns);
    }
    else if(it->is_function_call())
    {
      s_it->second.values.replace_const(
        to_code_function_call(it->code).function());
      simplify_expr(to_code_function_call(it->code).function(), ns);

      exprt::operandst &args =
        to_code_function_call(it->code).arguments();

      for(exprt::operandst::iterator o_it = args.begin();
          o_it != args.end(); ++o_it)
      {
        s_it->second.values.replace_const(*o_it);
        *o_it = simplify_expr(*o_it, ns);
      }
    }
    else if(it->is_other())
    {
      if(it->code.get_statement()==ID_expression)
        s_it->second.values.replace_const(it->code);
    }
  }
}

/*******************************************************************\

Function: constant_propagator_ait::replace_types_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_ait::replace_types_rec(
  const replace_symbolt &replace_const,
  exprt &expr)
{
  replace_const(expr.type());

  Forall_operands(it, expr)
    replace_types_rec(replace_const, *it);
}

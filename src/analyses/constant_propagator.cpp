/*******************************************************************\

Module: Constant Propagation

Author: Peter Schrammel

\*******************************************************************/

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
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns)
{
  if(lhs.id()!=ID_symbol)
    return;

  const symbol_exprt &s=to_symbol_expr(lhs);

  exprt tmp=rhs;
  values.replace_const(tmp);
  tmp=simplify_expr(tmp, ns);

  if(tmp.is_constant())
    values.set_to(s, tmp);
  else
    values.set_to_top(s);
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
  std::cout << "Transform from/to:\n";
  std::cout << from->location_number << " --> "
            << to->location_number << '\n';
#endif

#ifdef DEBUG
  std::cout << "Before:\n";
  output(std::cout, ai, ns);
#endif

  const constant_propagator_ait *cp=
    dynamic_cast<constant_propagator_ait *>(&ai);
  bool have_dirty=cp!=NULL;

  if(values.is_bottom)
    return;

  if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    const symbol_exprt &symbol=to_symbol_expr(code_decl.symbol());
    values.set_to_top(symbol);
  }
  else if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    const exprt &lhs=assignment.lhs();
    const exprt &rhs=assignment.rhs();
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
      g=simplify_expr(from->guard, ns);
    else
      g=simplify_expr(not_exprt(from->guard), ns);

    if(g.is_false())
     values.set_to_bottom();
    else
    {
      two_way_propagate_rec(g, ns);
    }
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    values.set_to_top(to_symbol_expr(code_dead.symbol()));
  }
  else if(from->is_function_call())
  {
    const code_function_callt &function_call=to_code_function_call(from->code);
    const exprt &function=function_call.function();

    locationt next=from;
    next++;

    if(function.id()==ID_symbol)
    {
      // called function identifier
      const symbol_exprt &symbol_expr=to_symbol_expr(function);
      const irep_idt id=symbol_expr.get_identifier();

      if(to==next)
      {
        if(id=="__CPROVER_set_must" ||
           id=="__CPROVER_get_must" ||
           id=="__CPROVER_set_may" ||
           id=="__CPROVER_get_may" ||
           id=="__CPROVER_cleanup" ||
           id=="__CPROVER_clear_may" ||
           id=="__CPROVER_clear_must")
        {
          // no effect on constants
        }
        else
        {
          if(have_dirty)
            values.set_dirty_to_top(cp->dirty, ns);
          else
            values.set_to_top();
        }
      }
      else
      {
        // we have an actual call

        // parameters of called function
        const symbolt &symbol=ns.lookup(id);
        const code_typet &code_type=to_code_type(symbol.type);
        const code_typet::parameterst &parameters=code_type.parameters();

        const code_function_callt::argumentst &arguments
          =function_call.arguments();

        unsigned n=std::min(arguments.size(), parameters.size());

        for(unsigned i=0; i<n; i++)
        {
          const symbol_exprt &parameter_expr
            =symbol_exprt(parameters[i].get_identifier(), arguments[i].type());

          assign_rec(values, parameter_expr, arguments[i], ns);
        }
      }
    }
    else
    {
      // unresolved call

      assert(to==next);

      if(have_dirty)
        values.set_dirty_to_top(cp->dirty, ns);
      else
        values.set_to_top();
    }
  }
  else if(from->is_end_function())
  {
    // erase parameters

    const irep_idt id=from->function;
    const symbolt &symbol=ns.lookup(id);

    const code_typet &type=to_code_type(symbol.type);

    typedef code_typet::parameterst parameterst;
    const parameterst &parameters=type.parameters();

    for(parameterst::const_iterator it=parameters.begin();
        it!=parameters.end(); it++)
    {
      // normal parameter
      const irep_idt par=it->get_identifier();

      // this erases the parameter from the map
      values.set_to_top(par);
    }
  }

#ifdef DEBUG
  std::cout << "After:\n";
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

  bool change=false;

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
    const exprt &lhs=expr.op0();
    const exprt &rhs=expr.op1();

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

Function: constant_propagator_domaint::domain_simplify

  Inputs: The condition to simplify and its namespace.

 Outputs: The simplified condition.

 Purpose: Simplify the condition given context-sensitive knowledge
          from the domain.

\*******************************************************************/

exprt constant_propagator_domaint::domain_simplify(
  const exprt &condition,
  const namespacet &ns,
  const bool lhs) const
{
  if(lhs)
  {
    // For now do not simplify the left hand sides of assignments
    return condition;
  }
  else
  {
    exprt e(condition);
    values.replace_const(e);
    return simplify_expr(e, ns);
  }
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
    if(replace_const.expr_map.find(to_symbol_expr(expr).get_identifier())==
       replace_const.expr_map.end())
      return false;

  if(expr.id()==ID_index)
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

 Purpose: Do not call when iterating over replace_const.expr_map!

\*******************************************************************/

bool constant_propagator_domaint::valuest::set_to_top(const irep_idt &id)
{
  replace_symbolt::expr_mapt::iterator r_it
    =replace_const.expr_map.find(id);

  if(r_it!=replace_const.expr_map.end())
  {
    assert(!is_bottom);
    replace_const.expr_map.erase(r_it);
    return true;
  }

  return false;
}

/*******************************************************************\

Function: constant_propagator_domaint::valuest::set_dirty_to_top

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_propagator_domaint::valuest::set_dirty_to_top(
  const dirtyt &dirty,
  const namespacet &ns)
{
  typedef replace_symbol_extt::expr_mapt expr_mapt;
  expr_mapt &expr_map=replace_const.expr_map;

  for(expr_mapt::iterator it=expr_map.begin();
      it!=expr_map.end();)
  {
    const irep_idt id=it->first;

    const symbolt &symbol=ns.lookup(id);

    if((!symbol.is_procedure_local() || dirty(id)) &&
       !symbol.type.get_bool(ID_C_constant))
      it=expr_map.erase(it);
    else
      it++;
  }
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
  {
    out << "  bottom\n";
    assert(replace_const.expr_map.empty());
    return;
  }

  assert(!is_bottom);
  if(replace_const.expr_map.empty())
  {
    out << "top\n";
    return;
  }

  for(replace_symbolt::expr_mapt::const_iterator
      it=replace_const.expr_map.begin();
      it!=replace_const.expr_map.end();
      ++it)
  {
    out << ' ' << it->first << "=" << from_expr(ns, "", it->second) << '\n';
  }
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
  // dummy
  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  // nothing to do
  if(src.is_bottom)
    return false;

  // just copy
  if(is_bottom)
  {
    assert(!src.is_bottom);
    replace_const=src.replace_const; // copy
    is_bottom=false;
    return true;
  }

  assert(!is_bottom && !src.is_bottom);

  bool changed=false;

  replace_symbol_extt::expr_mapt &expr_map=replace_const.expr_map;
  const replace_symbol_extt::expr_mapt &src_expr_map=src.replace_const.expr_map;

  // handle top
  if(src_expr_map.empty())
  {
    // change if it was not top
    changed=!expr_map.empty();

    set_to_top();
    assert(expr_map.empty());
    assert(!is_bottom);

    return changed;
  }

  // remove those that are
  // - different in src
  // - do not exist in src
  for(replace_symbolt::expr_mapt::iterator it=expr_map.begin();
      it!=expr_map.end();)
  {
    const irep_idt id=it->first;
    const exprt &expr=it->second;

    replace_symbolt::expr_mapt::const_iterator s_it;
    s_it=src_expr_map.find(id);

    if(s_it!=src_expr_map.end())
    {
      // check value
      const exprt &src_expr=s_it->second;

      if(expr!=src_expr)
      {
        it=expr_map.erase(it);
        changed=true;
      }
      else
        it++;
    }
    else
    {
      it=expr_map.erase(it);
      changed=true;
    }
  }

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

  for(replace_symbolt::expr_mapt::const_iterator
      it=src.replace_const.expr_map.begin();
      it!=src.replace_const.expr_map.end();
      ++it)
  {
    replace_symbolt::expr_mapt::iterator
      c_it = replace_const.expr_map.find(it->first);

    if(c_it!=replace_const.expr_map.end())
    {
      if(c_it->second!=it->second)
      {
        set_to_bottom();
        changed = true;
        break;
      }
    }
    else
    {
      set_to(it->first, it->second);
      changed = true;
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
  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

#if 0
  if(to->is_skip())
  {
    std::cout << "This:\n";
    values.output(std::cout, ns);
    std::cout << "Other:\n";
    other.values.output(std::cout, ns);
  }
#endif

  bool b;
  b=values.merge(other.values);

#if 0
  if(to->is_skip())
  {
    std::cout << "Merge result:\n";
    values.output(std::cout, ns);
  }
#endif

  return b;
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
    state_mapt::iterator s_it=state_map.find(it);

    if(s_it==state_map.end())
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
      exprt &rhs=to_code_assign(it->code).rhs();
      s_it->second.values.replace_const(rhs);
      rhs=simplify_expr(rhs, ns);
      if(rhs.id()==ID_constant)
        rhs.add_source_location()=it->code.op0().source_location();
    }
    else if(it->is_function_call())
    {
      s_it->second.values.replace_const(
        to_code_function_call(it->code).function());
      simplify_expr(to_code_function_call(it->code).function(), ns);

      exprt::operandst &args=
        to_code_function_call(it->code).arguments();

      for(exprt::operandst::iterator o_it=args.begin();
          o_it!=args.end(); ++o_it)
      {
        s_it->second.values.replace_const(*o_it);
        *o_it=simplify_expr(*o_it, ns);
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

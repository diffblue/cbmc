/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Constant Propagation

#include "constant_propagator.h"

#ifdef DEBUG
#include <iostream>
#include <util/format_expr.h>
#endif

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/ieee_float.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

#include <algorithm>
#include <array>

void constant_propagator_domaint::assign_rec(
  valuest &dest_values,
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  const constant_propagator_ait *cp)
{
  if(lhs.id()!=ID_symbol)
    return;

  if(cp && !cp->should_track_value(lhs, ns))
    return;

  const symbol_exprt &s=to_symbol_expr(lhs);

  exprt tmp=rhs;
  partial_evaluate(dest_values, tmp, ns);

  if(dest_values.is_constant(tmp))
  {
    DATA_INVARIANT(
      base_type_eq(ns.lookup(s).type, tmp.type(), ns),
      "type of constant to be replaced should match");
    dest_values.set_to(s, tmp);
  }
  else
    dest_values.set_to_top(s);
}

void constant_propagator_domaint::transform(
  const irep_idt &function_from,
  locationt from,
  const irep_idt &function_to,
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

  // When the domain is used with constant_propagator_ait,
  // information about dirty variables and config flags are
  // available. Otherwise, the below will be null and we use default
  // values
  const constant_propagator_ait *cp=
    dynamic_cast<constant_propagator_ait *>(&ai);
  bool have_dirty=(cp!=nullptr);

  // Transform on a domain that is bottom is possible
  // if a branch is impossible the target can still wind
  // up on the work list.
  if(values.is_bottom)
    return;

  if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    const symbol_exprt &symbol = code_decl.symbol();
    values.set_to_top(symbol);
  }
  else if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    const exprt &lhs=assignment.lhs();
    const exprt &rhs=assignment.rhs();
    assign_rec(values, lhs, rhs, ns, cp);
  }
  else if(from->is_assume())
  {
    two_way_propagate_rec(from->guard, ns, cp);
  }
  else if(from->is_goto())
  {
    exprt g;

    // Comparing iterators is safe as the target must be within the same list
    // of instructions because this is a GOTO.
    if(from->get_target()==to)
      g = from->guard;
    else
      g = not_exprt(from->guard);
    partial_evaluate(values, g, ns);
    if(g.is_false())
     values.set_to_bottom();
    else
    {
      two_way_propagate_rec(g, ns, cp);
      // If two way propagate is enabled then it may be possible to detect
      // that the branch condition is infeasible and thus the domain should
      // be set to bottom.  Without it the domain will only be set to bottom
      // if the guard expression is trivially (i.e. without context) false.
      INVARIANT(!values.is_bottom,
                "Without two-way propagation this should be impossible.");
    }
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    values.set_to_top(code_dead.symbol());
  }
  else if(from->is_function_call())
  {
    const code_function_callt &function_call=to_code_function_call(from->code);
    const exprt &function=function_call.function();

    if(function.id()==ID_symbol)
    {
      // called function identifier
      const symbol_exprt &symbol_expr=to_symbol_expr(function);
      const irep_idt id=symbol_expr.get_identifier();

      // Functions with no body
      if(function_from == function_to)
      {
        if(id==CPROVER_PREFIX "set_must" ||
           id==CPROVER_PREFIX "get_must" ||
           id==CPROVER_PREFIX "set_may" ||
           id==CPROVER_PREFIX "get_may" ||
           id==CPROVER_PREFIX "cleanup" ||
           id==CPROVER_PREFIX "clear_may" ||
           id==CPROVER_PREFIX "clear_must")
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

        const code_function_callt::argumentst &arguments=
          function_call.arguments();

        code_typet::parameterst::const_iterator p_it=parameters.begin();
        for(const auto &arg : arguments)
        {
          if(p_it==parameters.end())
            break;

          const symbol_exprt parameter_expr(p_it->get_identifier(), arg.type());
          assign_rec(values, parameter_expr, arg, ns, cp);

          ++p_it;
        }
      }
    }
    else
    {
      // unresolved call
      INVARIANT(
        function_from == function_to,
        "Unresolved call can only be approximated if a skip");

      if(have_dirty)
        values.set_dirty_to_top(cp->dirty, ns);
      else
        values.set_to_top();
    }
  }
  else if(from->is_end_function())
  {
    // erase parameters

    const irep_idt id = function_from;
    const symbolt &symbol=ns.lookup(id);

    const code_typet &type=to_code_type(symbol.type);

    for(const auto &param : type.parameters())
      values.set_to_top(symbol_exprt(param.get_identifier(), param.type()));
  }

  INVARIANT(from->is_goto() || !values.is_bottom,
            "Transform only sets bottom by using branch conditions");

#ifdef DEBUG
  std::cout << "After:\n";
  output(std::cout, ai, ns);
#endif
}


/// handles equalities and conjunctions containing equalities
bool constant_propagator_domaint::two_way_propagate_rec(
  const exprt &expr,
  const namespacet &ns,
  const constant_propagator_ait *cp)
{
#ifdef DEBUG
  std::cout << "two_way_propagate_rec: " << format(expr) << '\n';
#endif

  bool change=false;

  if(expr.id()==ID_and)
  {
    // need a fixed point here to get the most out of it
    do
    {
      change = false;

      forall_operands(it, expr)
        if(two_way_propagate_rec(*it, ns, cp))
          change=true;
    }
    while(change);
  }
  else if(expr.id()==ID_equal)
  {
    const exprt &lhs=expr.op0();
    const exprt &rhs=expr.op1();

    // two-way propagation
    valuest copy_values=values;
    assign_rec(copy_values, lhs, rhs, ns, cp);
    if(!values.is_constant(rhs) || values.is_constant(lhs))
      assign_rec(values, rhs, lhs, ns, cp);
    change = values.meet(copy_values, ns);
  }

#ifdef DEBUG
  std::cout << "two_way_propagate_rec: " << change << '\n';
#endif

  return change;
}

/// Simplify the condition given context-sensitive knowledge from the abstract
/// state.
/// \par parameters: The condition to simplify and its namespace.
/// \return The simplified condition.
bool constant_propagator_domaint::ai_simplify(
  exprt &condition,
  const namespacet &ns) const
{
  return partial_evaluate(values, condition, ns);
}


bool constant_propagator_domaint::valuest::is_constant(const exprt &expr) const
{
  class constant_propagator_is_constantt : public is_constantt
  {
  public:
    explicit constant_propagator_is_constantt(
      const replace_symbolt &replace_const)
      : replace_const(replace_const)
    {
    }

  protected:
    bool is_constant(const exprt &expr) const override
    {
      if(expr.id() == ID_symbol)
      {
        return replace_const.replaces_symbol(
          to_symbol_expr(expr).get_identifier());
      }

      return is_constantt::is_constant(expr);
    }

    const replace_symbolt &replace_const;
  };

  return constant_propagator_is_constantt(replace_const)(expr);
}

/// Do not call this when iterating over replace_const.expr_map!
bool constant_propagator_domaint::valuest::set_to_top(
  const symbol_exprt &symbol_expr)
{
  const auto n_erased = replace_const.erase(symbol_expr.get_identifier());

  INVARIANT(n_erased==0 || !is_bottom, "bottom should have no elements at all");

  return n_erased>0;
}


void constant_propagator_domaint::valuest::set_dirty_to_top(
  const dirtyt &dirty,
  const namespacet &ns)
{
  typedef replace_symbolt::expr_mapt expr_mapt;
  expr_mapt &expr_map = replace_const.get_expr_map();

  for(expr_mapt::iterator it=expr_map.begin();
      it!=expr_map.end();)
  {
    const irep_idt id=it->first;

    const symbolt &symbol=ns.lookup(id);

    if((!symbol.is_procedure_local() || dirty(id)) &&
       !symbol.type.get_bool(ID_C_constant))
    {
      it = replace_const.erase(it);
    }
    else
      it++;
  }
}

void constant_propagator_domaint::valuest::output(
  std::ostream &out,
  const namespacet &ns) const
{
  out << "const map:\n";

  if(is_bottom)
  {
    out << "  bottom\n";
    DATA_INVARIANT(is_empty(),
                   "If the domain is bottom, the map must be empty");
    return;
  }

  INVARIANT(!is_bottom, "Have handled bottom");
  if(is_empty())
  {
    out << "top\n";
    return;
  }

  for(const auto &p : replace_const.get_expr_map())
  {
    out << ' ' << p.first << "=" << from_expr(ns, p.first, p.second) << '\n';
  }
}

void constant_propagator_domaint::output(
  std::ostream &out,
  const ai_baset &,
  const namespacet &ns) const
{
  values.output(out, ns);
}

/// join
/// \return Return true if "this" has changed.
bool constant_propagator_domaint::valuest::merge(const valuest &src)
{
  // nothing to do
  if(src.is_bottom)
    return false;

  // just copy
  if(is_bottom)
  {
    PRECONDITION(!src.is_bottom);
    replace_const=src.replace_const; // copy
    is_bottom=false;
    return true;
  }

  INVARIANT(!is_bottom && !src.is_bottom, "Case handled");

  bool changed=false;

  // handle top
  if(src.is_empty())
  {
    // change if it was not top
    changed = !is_empty();

    set_to_top();

    return changed;
  }

  replace_symbolt::expr_mapt &expr_map = replace_const.get_expr_map();
  const replace_symbolt::expr_mapt &src_expr_map =
    src.replace_const.get_expr_map();

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
        it = replace_const.erase(it);
        changed=true;
      }
      else
        it++;
    }
    else
    {
      it = replace_const.erase(it);
      changed=true;
    }
  }

  return changed;
}

/// meet
/// \return Return true if "this" has changed.
bool constant_propagator_domaint::valuest::meet(
  const valuest &src,
  const namespacet &ns)
{
  if(src.is_bottom || is_bottom)
    return false;

  bool changed=false;

  for(const auto &m : src.replace_const.get_expr_map())
  {
    replace_symbolt::expr_mapt::const_iterator c_it =
      replace_const.get_expr_map().find(m.first);

    if(c_it != replace_const.get_expr_map().end())
    {
      if(c_it->second!=m.second)
      {
        set_to_bottom();
        changed=true;
        break;
      }
    }
    else
    {
      const typet &m_id_type = ns.lookup(m.first).type;
      DATA_INVARIANT(
        base_type_eq(m_id_type, m.second.type(), ns),
        "type of constant to be stored should match");
      set_to(symbol_exprt(m.first, m_id_type), m.second);
      changed=true;
    }
  }

  return changed;
}

/// \return Return true if "this" has changed.
bool constant_propagator_domaint::merge(
  const constant_propagator_domaint &other,
  locationt,
  locationt)
{
  return values.merge(other.values);
}

/// Attempt to evaluate expression using domain knowledge
/// This function changes the expression that is passed into it.
/// \param known_values: The constant values under which to evaluate \p expr
/// \param expr The expression to evaluate
/// \param ns The namespace for symbols in the expression
/// \return True if the expression is unchanged, false otherwise
bool constant_propagator_domaint::partial_evaluate(
  const valuest &known_values,
  exprt &expr,
  const namespacet &ns)
{
  // if the current rounding mode is top we can
  // still get a non-top result by trying all rounding
  // modes and checking if the results are all the same
  if(!known_values.is_constant(symbol_exprt(ID_cprover_rounding_mode_str)))
  {
    return partial_evaluate_with_all_rounding_modes(known_values, expr, ns);
  }
  return replace_constants_and_simplify(known_values, expr, ns);
}

/// Attempt to evaluate an expression in all rounding modes.
///
/// \param known_values: The constant values under which to evaluate \p expr
/// \param expr The expression to evaluate
/// \param ns The namespace for symbols in the expression
/// \return If the result is the same for all rounding modes, change
/// expr to that result and return false. Otherwise, return true.
bool constant_propagator_domaint::partial_evaluate_with_all_rounding_modes(
  const valuest &known_values,
  exprt &expr,
  const namespacet &ns)
{ // NOLINTNEXTLINE (whitespace/braces)
  auto rounding_modes = std::array<ieee_floatt::rounding_modet, 4>{
    // NOLINTNEXTLINE (whitespace/braces)
    {ieee_floatt::ROUND_TO_EVEN,
     ieee_floatt::ROUND_TO_ZERO,
     ieee_floatt::ROUND_TO_MINUS_INF,
     // NOLINTNEXTLINE (whitespace/braces)
     ieee_floatt::ROUND_TO_PLUS_INF}};
  exprt first_result;
  for(std::size_t i = 0; i < rounding_modes.size(); ++i)
  {
    valuest tmp_values = known_values;
    tmp_values.set_to(
      symbol_exprt(ID_cprover_rounding_mode_str, integer_typet()),
      from_integer(rounding_modes[i], integer_typet()));
    exprt result = expr;
    if(replace_constants_and_simplify(tmp_values, result, ns))
    {
      return true;
    }
    else if(i == 0)
    {
      first_result = result;
    }
    else if(result != first_result)
    {
      return true;
    }
  }
  expr = first_result;
  return false;
}

bool constant_propagator_domaint::replace_constants_and_simplify(
  const valuest &known_values,
  exprt &expr,
  const namespacet &ns)
{
  bool did_not_change_anything = true;

  // iterate constant propagation and simplification until we cannot
  // constant-propagate any further - a prime example is pointer dereferencing,
  // where constant propagation may have a value of the pointer, the simplifier
  // takes care of evaluating dereferencing, and we might then have the value of
  // the resulting symbol known to constant propagation and thus replace the
  // dereferenced expression by a constant
  while(!known_values.replace_const.replace(expr))
  {
    did_not_change_anything = false;
    simplify(expr, ns);
  }

  // even if we haven't been able to constant-propagate anything, run the
  // simplifier on the expression
  if(did_not_change_anything)
    did_not_change_anything &= simplify(expr, ns);

  return did_not_change_anything;
}

void constant_propagator_ait::replace(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  Forall_goto_functions(f_it, goto_functions)
    replace(f_it->second, ns);
}


void constant_propagator_ait::replace(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  Forall_goto_program_instructions(it, goto_function.body)
  {
    // Works because this is a location (but not history) sensitive domain
    const constant_propagator_domaint &d = (*this)[it];

    if(d.is_bottom())
      continue;

    replace_types_rec(d.values.replace_const, it->code);
    replace_types_rec(d.values.replace_const, it->guard);

    if(it->is_goto() || it->is_assume() || it->is_assert())
    {
      constant_propagator_domaint::partial_evaluate(d.values, it->guard, ns);
    }
    else if(it->is_assign())
    {
      exprt &rhs=to_code_assign(it->code).rhs();
      constant_propagator_domaint::partial_evaluate(d.values, rhs, ns);

      if(rhs.id()==ID_constant)
        rhs.add_source_location() =
          to_code_assign(it->code).lhs().source_location();
    }
    else if(it->is_function_call())
    {
      exprt &function = to_code_function_call(it->code).function();
      constant_propagator_domaint::partial_evaluate(d.values, function, ns);

      exprt::operandst &args=
        to_code_function_call(it->code).arguments();

      for(auto &arg : args)
      {
        constant_propagator_domaint::partial_evaluate(d.values, arg, ns);
      }
    }
    else if(it->is_other())
    {
      if(it->code.get_statement()==ID_expression)
      {
        constant_propagator_domaint::partial_evaluate(d.values, it->code, ns);
      }
    }
  }
}

void constant_propagator_ait::replace_types_rec(
  const replace_symbolt &replace_const,
  exprt &expr)
{
  replace_const(expr.type());

  Forall_operands(it, expr)
    replace_types_rec(replace_const, *it);
}

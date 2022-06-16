/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Constant Propagation

#include "constant_propagator.h"

#include <goto-programs/adjust_float_expressions.h>

#ifdef DEBUG
#include <iostream>
#include <util/format_expr.h>
#endif

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/ieee_float.h>
#include <util/mathematical_types.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>

#include <langapi/language_util.h>

#include <algorithm>
#include <array>

/// Assign value `rhs` to `lhs`, recording any newly-known constants in
/// `dest_values`.
/// \param [out] dest_values: results of the assignment are recorded here. We
///   might add extra entries (if we determine some symbol is constant), or
///   might remove existing ones (if the lhs expression is unknown), except if
///   `is_assignment` is false, in which case only the former is done.
/// \param lhs: lhs expression to assign
/// \param rhs: rhs expression to assign to lhs
/// \param ns: namespace, used to check for type mismatches
/// \param cp: owning constant propagator instance, used to filter out symbols
///   that the user doesn't want tracked
/// \param is_assignment: if true, assign_rec may remove entries from
///   dest_values when a constant assignment cannot be determined. This is used
///   when an actual assignment instruction is processed. If false, new entries
///   can be added but existing ones will not be removed; this is used when the
///   "assignment" is actually implied by a read-only operation, such as passing
///   "IF x == y" -- if we know what 'y' is that tells us the value for x, but
///   if we don't there is no reason to discard pre-existing knowledge about x.
void constant_propagator_domaint::assign_rec(
  valuest &dest_values,
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  const constant_propagator_ait *cp,
  bool is_assignment)
{
  if(lhs.id() == ID_dereference)
  {
    exprt eval_lhs = lhs;
    if(partial_evaluate(dest_values, eval_lhs, ns))
    {
      if(is_assignment)
      {
        const bool have_dirty = (cp != nullptr);

        if(have_dirty)
          dest_values.set_dirty_to_top(cp->dirty, ns);
        else
          dest_values.set_to_top();
      }
      // Otherwise disregard this unknown deref in a read-only context.
    }
    else
      assign_rec(dest_values, eval_lhs, rhs, ns, cp, is_assignment);
  }
  else if(lhs.id() == ID_index)
  {
    const index_exprt &index_expr = to_index_expr(lhs);
    with_exprt new_rhs(index_expr.array(), index_expr.index(), rhs);
    assign_rec(dest_values, index_expr.array(), new_rhs, ns, cp, is_assignment);
  }
  else if(lhs.id() == ID_member)
  {
    const member_exprt &member_expr = to_member_expr(lhs);
    with_exprt new_rhs(member_expr.compound(), exprt(ID_member_name), rhs);
    new_rhs.where().set(ID_component_name, member_expr.get_component_name());
    assign_rec(
      dest_values, member_expr.compound(), new_rhs, ns, cp, is_assignment);
  }
  else if(lhs.id() == ID_symbol)
  {
    if(cp && !cp->should_track_value(lhs, ns))
      return;

    const symbol_exprt &s = to_symbol_expr(lhs);

    exprt tmp = rhs;
    partial_evaluate(dest_values, tmp, ns);

    if(dest_values.is_constant(tmp))
    {
      DATA_INVARIANT(
        ns.lookup(s).type == tmp.type(),
        "type of constant to be replaced should match");
      dest_values.set_to(s, tmp);
    }
    else
    {
      if(is_assignment)
        dest_values.set_to_top(s);
    }
  }
  else if(is_assignment)
  {
    // it's an assignment, but we don't really know what object is being written
    // to: assume it may write to anything.
    dest_values.set_to_top();
  }
}

void constant_propagator_domaint::transform(
  const irep_idt &function_from,
  trace_ptrt trace_from,
  const irep_idt &function_to,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from{trace_from->current_location()};
  locationt to{trace_to->current_location()};

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
    const symbol_exprt &symbol = from->decl_symbol();
    values.set_to_top(symbol);
  }
  else if(from->is_assign())
  {
    const exprt &lhs = from->assign_lhs();
    const exprt &rhs = from->assign_rhs();
    assign_rec(values, lhs, rhs, ns, cp, true);
  }
  else if(from->is_assume())
  {
    two_way_propagate_rec(from->condition(), ns, cp);
  }
  else if(from->is_goto())
  {
    exprt g;

    // Comparing iterators is safe as the target must be within the same list
    // of instructions because this is a GOTO.
    if(from->get_target()==to)
      g = from->condition();
    else
      g = not_exprt(from->condition());
    partial_evaluate(values, g, ns);
    
    if(g.is_false())
     values.set_to_bottom();
    else
      two_way_propagate_rec(g, ns, cp);
  }
  else if(from->is_dead())
  {
    values.set_to_top(from->dead_symbol());
  }
  else if(from->is_function_call())
  {
    const exprt &function = from->call_function();

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

        const code_function_callt::argumentst &arguments =
          from->call_arguments();

        code_typet::parameterst::const_iterator p_it=parameters.begin();
        for(const auto &arg : arguments)
        {
          if(p_it==parameters.end())
            break;

          const symbol_exprt parameter_expr(p_it->get_identifier(), arg.type());
          assign_rec(values, parameter_expr, arg, ns, cp, true);

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

static void
replace_typecast_of_bool(exprt &lhs, exprt &rhs, const namespacet &ns)
{
  // (int)var xx 0 ==> var xx (_Bool)0 or similar (xx is == or !=)
  // Note this is restricted to bools because in general turning a widening
  // into a narrowing typecast is not correct.
  if(lhs.id() != ID_typecast)
    return;

  const exprt &lhs_underlying = to_typecast_expr(lhs).op();
  if(
    lhs_underlying.type() == bool_typet() ||
    lhs_underlying.type() == c_bool_type())
  {
    rhs = typecast_exprt(rhs, lhs_underlying.type());
    simplify(rhs, ns);

    lhs = lhs_underlying;
  }
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
    bool change_this_time;
    do
    {
      change_this_time = false;

      forall_operands(it, expr)
      {
        change_this_time |= two_way_propagate_rec(*it, ns, cp);
        if(change_this_time)
          change = true;
      }
    } while(change_this_time);
  }
  else if(expr.id() == ID_not)
  {
    const auto &op = to_not_expr(expr).op();

    if(op.id() == ID_equal || op.id() == ID_notequal)
    {
      exprt subexpr = op;
      subexpr.id(subexpr.id() == ID_equal ? ID_notequal : ID_equal);
      change = two_way_propagate_rec(subexpr, ns, cp);
    }
    else if(op.id() == ID_symbol && expr.type() == bool_typet())
    {
      // Treat `IF !x` like `IF x == FALSE`:
      change = two_way_propagate_rec(equal_exprt(op, false_exprt()), ns, cp);
    }
  }
  else if(expr.id() == ID_symbol)
  {
    if(expr.type() == bool_typet())
    {
      // Treat `IF x` like `IF x == TRUE`:
      change = two_way_propagate_rec(equal_exprt(expr, true_exprt()), ns, cp);
    }
  }
  else if(expr.id() == ID_notequal)
  {
    // Treat "symbol != constant" like "symbol == !constant" when the constant
    // is a boolean.
    exprt lhs = to_notequal_expr(expr).lhs();
    exprt rhs = to_notequal_expr(expr).rhs();

    if(lhs.is_constant() && !rhs.is_constant())
      std::swap(lhs, rhs);

    if(lhs.is_constant() || !rhs.is_constant())
      return false;

    replace_typecast_of_bool(lhs, rhs, ns);

    if(lhs.type() != bool_typet() && lhs.type() != c_bool_type())
      return false;

    // x != FALSE ==> x == TRUE

    if(rhs.is_zero() || rhs.is_false())
      rhs = from_integer(1, rhs.type());
    else
      rhs = from_integer(0, rhs.type());

    change = two_way_propagate_rec(equal_exprt(lhs, rhs), ns, cp);
  }
  else if(expr.id() == ID_equal)
  {
    exprt lhs = to_equal_expr(expr).lhs();
    exprt rhs = to_equal_expr(expr).rhs();

    replace_typecast_of_bool(lhs, rhs, ns);

    // two-way propagation
    valuest copy_values=values;
    assign_rec(copy_values, lhs, rhs, ns, cp, false);
    if(!values.is_constant(rhs) || values.is_constant(lhs))
      assign_rec(values, rhs, lhs, ns, cp, false);
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

class constant_propagator_is_constantt : public is_constantt
{
public:
  explicit constant_propagator_is_constantt(
    const replace_symbolt &replace_const)
    : replace_const(replace_const)
  {
  }

  bool is_constant(const irep_idt &id) const
  {
    return replace_const.replaces_symbol(id);
  }

protected:
  bool is_constant(const exprt &expr) const override
  {
    if(expr.id() == ID_symbol)
      return is_constant(to_symbol_expr(expr).get_identifier());

    return is_constantt::is_constant(expr);
  }

  const replace_symbolt &replace_const;
};

bool constant_propagator_domaint::valuest::is_constant(const exprt &expr) const
{
  return constant_propagator_is_constantt(replace_const)(expr);
}

bool constant_propagator_domaint::valuest::is_constant(const irep_idt &id) const
{
  return constant_propagator_is_constantt(replace_const).is_constant(id);
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

    if(
      (symbol.is_static_lifetime || dirty(id)) &&
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
        m_id_type == m.second.type(),
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
  trace_ptrt,
  trace_ptrt)
{
  return values.merge(other.values);
}

/// Attempt to evaluate expression using domain knowledge
/// This function changes the expression that is passed into it.
/// \param known_values: The constant values under which to evaluate \p expr
/// \param expr: The expression to evaluate
/// \param ns: The namespace for symbols in the expression
/// \return True if the expression is unchanged, false otherwise
bool constant_propagator_domaint::partial_evaluate(
  const valuest &known_values,
  exprt &expr,
  const namespacet &ns)
{
  // if the current rounding mode is top we can
  // still get a non-top result by trying all rounding
  // modes and checking if the results are all the same
  if(!known_values.is_constant(rounding_mode_identifier()))
    return partial_evaluate_with_all_rounding_modes(known_values, expr, ns);

  return replace_constants_and_simplify(known_values, expr, ns);
}

/// Attempt to evaluate an expression in all rounding modes.
///
/// \param known_values: The constant values under which to evaluate \p expr
/// \param expr: The expression to evaluate
/// \param ns: The namespace for symbols in the expression
/// \return If the result is the same for all rounding modes, change
///   expr to that result and return false. Otherwise, return true.
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
      symbol_exprt(rounding_mode_identifier(), integer_typet()),
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
  for(auto &gf_entry : goto_functions.function_map)
    replace(gf_entry.second, ns);
}


void constant_propagator_ait::replace(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  Forall_goto_program_instructions(it, goto_function.body)
  {
    auto const current_domain_ptr =
      std::dynamic_pointer_cast<const constant_propagator_domaint>(
        this->abstract_state_before(it));
    const constant_propagator_domaint &d = *current_domain_ptr;

    /*
    // This condition does not optimize away the second GOTO in the code
    //         GOTO 32
    //         IF 0 ≠ 0 THEN GOTO 6
    // Perhaps instead of ignoring unreachable instructions, they can just be removed.

    if(d.is_bottom())
      continue;
    */

    replace_types_rec(d.values.replace_const, it->code_nonconst());

    if(it->is_goto() || it->is_assume() || it->is_assert())
    {
      exprt c = it->condition();
      replace_types_rec(d.values.replace_const, c);
      if(!constant_propagator_domaint::partial_evaluate(d.values, c, ns))
        it->condition_nonconst() = c;
    }
    else if(it->is_assign())
    {
      exprt &rhs = it->assign_rhs_nonconst();

      if(!constant_propagator_domaint::partial_evaluate(d.values, rhs, ns))
      {
        if(rhs.id() == ID_constant)
          rhs.add_source_location() = it->assign_lhs().source_location();
      }
    }
    else if(it->is_function_call())
    {
      constant_propagator_domaint::partial_evaluate(
        d.values, it->call_function(), ns);

      for(auto &arg : it->call_arguments())
        constant_propagator_domaint::partial_evaluate(d.values, arg, ns);
    }
    else if(it->is_other())
    {
      if(it->get_other().get_statement() == ID_expression)
      {
        auto c = to_code_expression(it->get_other());
        if(!constant_propagator_domaint::partial_evaluate(
             d.values, c.expression(), ns))
        {
          it->set_other(c);
        }
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

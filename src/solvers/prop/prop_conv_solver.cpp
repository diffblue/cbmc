/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop_conv_solver.h"

#include <util/range.h>

#include <algorithm>
#include <chrono>

#include "literal_expr.h"

bool prop_conv_solvert::is_in_conflict(const exprt &expr) const
{
  return prop.is_in_conflict(to_literal_expr(expr).get_literal());
}

void prop_conv_solvert::set_frozen(const bvt &bv)
{
  for(const auto &bit : bv)
    if(!bit.is_constant())
      set_frozen(bit);
}

void prop_conv_solvert::set_frozen(literalt a)
{
  prop.set_frozen(a);
}

void prop_conv_solvert::set_all_frozen()
{
  freeze_all = true;
}

exprt prop_conv_solvert::handle(const exprt &expr)
{
  // We can only improve Booleans.
  if(expr.type().id() != ID_bool)
    return expr;

  // We convert to a literal to obtain a 'small' handle
  literalt l = convert(expr);

  // The literal may be a constant as a result of non-trivial
  // propagation. We return constants as such.
  if(l.is_true())
    return true_exprt();
  else if(l.is_false())
    return false_exprt();

  // freeze to enable incremental use
  set_frozen(l);

  return literal_exprt(l);
}

literalt prop_conv_solvert::get_literal(const irep_idt &identifier)
{
  auto result =
    symbols.insert(std::pair<irep_idt, literalt>(identifier, literalt()));

  if(!result.second)
    return result.first->second;

  literalt literal = prop.new_variable();
  prop.set_variable_name(literal, identifier);

  // insert
  result.first->second = literal;

  return literal;
}

optionalt<bool> prop_conv_solvert::get_bool(const exprt &expr) const
{
  // trivial cases

  if(expr.is_true())
  {
    return true;
  }
  else if(expr.is_false())
  {
    return false;
  }
  else if(expr.id() == ID_symbol)
  {
    symbolst::const_iterator result =
      symbols.find(to_symbol_expr(expr).get_identifier());

    // This may fail if the symbol isn't Boolean or
    // not in the formula.
    if(result == symbols.end())
      return {};

    return prop.l_get(result->second).is_true();
  }
  else if(expr.id() == ID_literal)
  {
    return prop.l_get(to_literal_expr(expr).get_literal()).is_true();
  }

  // sub-expressions

  if(expr.id() == ID_not)
  {
    if(expr.type().id() == ID_bool)
    {
      auto tmp = get_bool(to_not_expr(expr).op());
      if(tmp.has_value())
        return !*tmp;
      else
        return {};
    }
  }
  else if(expr.id() == ID_and || expr.id() == ID_or)
  {
    if(expr.type().id() == ID_bool && expr.operands().size() >= 1)
    {
      forall_operands(it, expr)
      {
        auto tmp = get_bool(*it);
        if(!tmp.has_value())
          return {};

        if(expr.id() == ID_and)
        {
          if(*tmp == false)
            return false;
        }
        else // or
        {
          if(*tmp == true)
            return true;
        }
      }

      return expr.id() == ID_and;
    }
  }

  // check cache

  cachet::const_iterator cache_result = cache.find(expr);
  if(cache_result == cache.end())
    return {}; // not in formula
  else
    return prop.l_get(cache_result->second).is_true();
}

literalt prop_conv_solvert::convert(const exprt &expr)
{
  if(!use_cache || expr.id() == ID_symbol || expr.id() == ID_constant)
  {
    literalt literal = convert_bool(expr);
    if(freeze_all && !literal.is_constant())
      prop.set_frozen(literal);
    return literal;
  }

  // check cache first
  auto result = cache.insert({expr, literalt()});

  // get a reference to the cache entry
  auto &cache_entry = result.first->second;

  if(!result.second) // found in cache
    return cache_entry;

  // The following may invalidate the iterator result.first,
  // but note that the _reference_ is guaranteed to remain valid.
  literalt literal = convert_bool(expr);

  // store the literal in the cache using the reference
  cache_entry = literal;

  if(freeze_all && !literal.is_constant())
    prop.set_frozen(literal);

#if 0
  std::cout << literal << "=" << expr << '\n';
#endif

  return literal;
}

literalt prop_conv_solvert::convert_bool(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);

  const exprt::operandst &op = expr.operands();

  if(expr.is_constant())
  {
    if(expr.is_true())
      return const_literal(true);
    else
    {
      INVARIANT(
        expr.is_false(),
        "constant expression of type bool should be either true or false");
      return const_literal(false);
    }
  }
  else if(expr.id() == ID_symbol)
  {
    return get_literal(to_symbol_expr(expr).get_identifier());
  }
  else if(expr.id() == ID_literal)
  {
    return to_literal_expr(expr).get_literal();
  }
  else if(expr.id() == ID_nondet_symbol)
  {
    return prop.new_variable();
  }
  else if(expr.id() == ID_implies)
  {
    const implies_exprt &implies_expr = to_implies_expr(expr);
    return prop.limplies(
      convert(implies_expr.op0()), convert(implies_expr.op1()));
  }
  else if(expr.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(expr);
    return prop.lselect(
      convert(if_expr.cond()),
      convert(if_expr.true_case()),
      convert(if_expr.false_case()));
  }
  else if(expr.id() == ID_constraint_select_one)
  {
    DATA_INVARIANT(
      op.size() >= 2,
      "constraint_select_one should have at least two operands");

    std::vector<literalt> op_bv;
    op_bv.reserve(op.size());

    forall_operands(it, expr)
      op_bv.push_back(convert(*it));

    // add constraints

    bvt b;
    b.reserve(op_bv.size() - 1);

    for(unsigned i = 1; i < op_bv.size(); i++)
      b.push_back(prop.lequal(op_bv[0], op_bv[i]));

    prop.l_set_to_true(prop.lor(b));

    return op_bv[0];
  }
  else if(
    expr.id() == ID_or || expr.id() == ID_and || expr.id() == ID_xor ||
    expr.id() == ID_nor || expr.id() == ID_nand)
  {
    INVARIANT(
      !op.empty(),
      "operator '" + expr.id_string() + "' takes at least one operand");

    bvt bv;

    for(const auto &operand : op)
      bv.push_back(convert(operand));

    if(!bv.empty())
    {
      if(expr.id() == ID_or)
        return prop.lor(bv);
      else if(expr.id() == ID_nor)
        return !prop.lor(bv);
      else if(expr.id() == ID_and)
        return prop.land(bv);
      else if(expr.id() == ID_nand)
        return !prop.land(bv);
      else if(expr.id() == ID_xor)
        return prop.lxor(bv);
    }
  }
  else if(expr.id() == ID_not)
  {
    INVARIANT(op.size() == 1, "not takes one operand");
    return !convert(op.front());
  }
  else if(expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    INVARIANT(op.size() == 2, "equality takes two operands");
    bool equal = (expr.id() == ID_equal);

    if(op[0].type().id() == ID_bool && op[1].type().id() == ID_bool)
    {
      literalt tmp1 = convert(op[0]), tmp2 = convert(op[1]);
      return equal ? prop.lequal(tmp1, tmp2) : prop.lxor(tmp1, tmp2);
    }
  }

  return convert_rest(expr);
}

literalt prop_conv_solvert::convert_rest(const exprt &expr)
{
  // fall through
  ignoring(expr);
  return prop.new_variable();
}

bool prop_conv_solvert::set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation)
    return true;

  // optimization for constraint of the form
  // new_variable = value

  if(expr.lhs().id() == ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(expr.lhs()).get_identifier();

    literalt tmp = convert(expr.rhs());

    std::pair<symbolst::iterator, bool> result =
      symbols.insert(std::pair<irep_idt, literalt>(identifier, tmp));

    if(result.second)
      return false; // ok, inserted!

    // nah, already there
  }

  return true;
}

void prop_conv_solvert::add_constraints_to_prop(const exprt &expr, bool value)
{
  PRECONDITION(expr.type().id() == ID_bool);

  const bool has_only_boolean_operands = std::all_of(
    expr.operands().begin(), expr.operands().end(), [](const exprt &expr) {
      return expr.type().id() == ID_bool;
    });

  if(has_only_boolean_operands)
  {
    if(expr.id() == ID_not)
    {
      add_constraints_to_prop(to_not_expr(expr).op(), !value);
      return;
    }
    else
    {
      if(value)
      {
        // set_to_true

        if(expr.id() == ID_and)
        {
          forall_operands(it, expr)
            add_constraints_to_prop(*it, true);

          return;
        }
        else if(expr.id() == ID_or)
        {
          // Special case for a CNF-clause,
          // i.e., a constraint that's a disjunction.

          if(!expr.operands().empty())
          {
            bvt bv;
            bv.reserve(expr.operands().size());

            forall_operands(it, expr)
              bv.push_back(convert(*it));

            prop.lcnf(bv);
            return;
          }
        }
        else if(expr.id() == ID_implies)
        {
          const auto &implies_expr = to_implies_expr(expr);
          literalt l_lhs = convert(implies_expr.lhs());
          literalt l_rhs = convert(implies_expr.rhs());
          prop.lcnf(!l_lhs, l_rhs);
          return;
        }
        else if(expr.id() == ID_equal)
        {
          if(!set_equality_to_true(to_equal_expr(expr)))
            return;
        }
      }
      else
      {
        // set_to_false
        if(expr.id() == ID_implies) // !(a=>b)  ==  (a && !b)
        {
          const implies_exprt &implies_expr = to_implies_expr(expr);

          add_constraints_to_prop(implies_expr.op0(), true);
          add_constraints_to_prop(implies_expr.op1(), false);
          return;
        }
        else if(expr.id() == ID_or) // !(a || b)  ==  (!a && !b)
        {
          forall_operands(it, expr)
            add_constraints_to_prop(*it, false);
          return;
        }
      }
    }
  }

  // fall back to convert
  prop.l_set_to(convert(expr), value);
}

void prop_conv_solvert::ignoring(const exprt &expr)
{
  // fall through

  log.warning() << "warning: ignoring " << expr.pretty() << messaget::eom;
}

void prop_conv_solvert::finish_eager_conversion()
{
}

decision_proceduret::resultt prop_conv_solvert::dec_solve()
{
  // post-processing isn't incremental yet
  if(!post_processing_done)
  {
    const auto post_process_start = std::chrono::steady_clock::now();

    log.statistics() << "Post-processing" << messaget::eom;
    finish_eager_conversion();
    post_processing_done = true;

    const auto post_process_stop = std::chrono::steady_clock::now();
    std::chrono::duration<double> post_process_runtime =
      std::chrono::duration<double>(post_process_stop - post_process_start);
    log.status() << "Runtime Post-process: " << post_process_runtime.count()
                 << "s" << messaget::eom;
  }

  log.statistics() << "Solving with " << prop.solver_text() << messaget::eom;

  switch(prop.prop_solve())
  {
  case propt::resultt::P_SATISFIABLE:
    return resultt::D_SATISFIABLE;
  case propt::resultt::P_UNSATISFIABLE:
    return resultt::D_UNSATISFIABLE;
  case propt::resultt::P_ERROR:
    return resultt::D_ERROR;
  }

  UNREACHABLE;
}

exprt prop_conv_solvert::get(const exprt &expr) const
{
  if(expr.type().id() == ID_bool)
  {
    auto value = get_bool(expr);

    if(value.has_value())
    {
      if(*value)
        return true_exprt();
      else
        return false_exprt();
    }
  }

  exprt tmp = expr;
  for(auto &op : tmp.operands())
  {
    exprt tmp_op = get(op);
    op.swap(tmp_op);
  }
  return tmp;
}

void prop_conv_solvert::print_assignment(std::ostream &out) const
{
  for(const auto &symbol : symbols)
    out << symbol.first << " = " << prop.l_get(symbol.second) << '\n';
}

std::size_t prop_conv_solvert::get_number_of_solver_calls() const
{
  return prop.get_number_of_solver_calls();
}

const char *prop_conv_solvert::context_prefix = "prop_conv::context$";

void prop_conv_solvert::set_to(const exprt &expr, bool value)
{
  if(assumption_stack.empty())
  {
    // We are in the root context.
    add_constraints_to_prop(expr, value);
  }
  else
  {
    // We have a child context. We add context_literal ==> expr to the formula.
    add_constraints_to_prop(
      or_exprt(literal_exprt(!assumption_stack.back()), expr), value);
  }
}

void prop_conv_solvert::push(const std::vector<exprt> &assumptions)
{
  // We push the given assumptions as a single context onto the stack.
  assumption_stack.reserve(assumption_stack.size() + assumptions.size());
  for(const auto &assumption : assumptions)
    assumption_stack.push_back(to_literal_expr(assumption).get_literal());
  context_size_stack.push_back(assumptions.size());

  prop.set_assumptions(assumption_stack);
}

void prop_conv_solvert::push()
{
  // We create a new context literal.
  literalt context_literal = convert(symbol_exprt(
    context_prefix + std::to_string(context_literal_counter++), bool_typet()));

  assumption_stack.push_back(context_literal);
  context_size_stack.push_back(1);

  prop.set_assumptions(assumption_stack);
}

void prop_conv_solvert::pop()
{
  // We remove the context from the stack.
  assumption_stack.resize(assumption_stack.size() - context_size_stack.back());
  context_size_stack.pop_back();

  prop.set_assumptions(assumption_stack);
}

// This method out-of-line because gcc-5.5.0-12ubuntu1 20171010 miscompiles it
// when inline (in certain build configurations, notably -O2 -g0) by producing
// a non-virtual thunk with c++03 ABI but a function body with c++11 ABI, the
// mismatch leading to a missing vtable entry and consequent null-pointer deref
// whenever this function is called.
std::string prop_conv_solvert::decision_procedure_text() const
{
  return "propositional reduction";
}

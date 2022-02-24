/*******************************************************************\

Module: Java trace validation

Author: Jeannie Moulton

\*******************************************************************/

#include "java_trace_validation.h"

#include <algorithm>

#include <goto-programs/goto_trace.h>

#include <util/byte_operators.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

bool check_symbol_structure(const exprt &expr)
{
  const auto symbol = expr_try_dynamic_cast<symbol_exprt>(expr);
  return symbol && !symbol->get_identifier().empty();
}

/// \return true iff the expression is a symbol or is an expression whose first
/// operand can contain a nested symbol
static bool may_be_lvalue(const exprt &expr)
{
  return can_cast_expr<member_exprt>(expr) ||
         can_cast_expr<index_exprt>(expr) ||
         can_cast_expr<address_of_exprt>(expr) ||
         can_cast_expr<typecast_exprt>(expr) ||
         can_cast_expr<symbol_exprt>(expr) ||
         can_cast_expr<byte_extract_exprt>(expr);
}

optionalt<symbol_exprt> get_inner_symbol_expr(exprt expr)
{
  while(expr.has_operands())
  {
    expr = to_multi_ary_expr(expr).op0();
    if(!may_be_lvalue(expr))
      return {};
  }
  if(!check_symbol_structure(expr))
    return {};
  return *expr_try_dynamic_cast<symbol_exprt>(expr);
}

bool check_member_structure(const member_exprt &expr)
{
  if(!expr.has_operands())
    return false;
  const auto symbol_operand = get_inner_symbol_expr(expr);
  return symbol_operand.has_value();
}

bool valid_lhs_expr_high_level(const exprt &lhs)
{
  return can_cast_expr<member_exprt>(lhs) || can_cast_expr<symbol_exprt>(lhs) ||
         can_cast_expr<index_exprt>(lhs) ||
         can_cast_expr<byte_extract_exprt>(lhs);
}

bool valid_rhs_expr_high_level(const exprt &rhs)
{
  return can_cast_expr<struct_exprt>(rhs) || can_cast_expr<array_exprt>(rhs) ||
         can_cast_expr<constant_exprt>(rhs) ||
         can_cast_expr<annotated_pointer_constant_exprt>(rhs) ||
         can_cast_expr<address_of_exprt>(rhs) ||
         can_cast_expr<symbol_exprt>(rhs) ||
         can_cast_expr<array_list_exprt>(rhs) ||
         can_cast_expr<byte_extract_exprt>(rhs);
}

bool can_evaluate_to_constant(const exprt &expression)
{
  return can_cast_expr<constant_exprt>(skip_typecast(expression)) ||
         can_cast_expr<symbol_exprt>(skip_typecast(expression)) ||
         can_cast_expr<plus_exprt>(skip_typecast(expression));
}

bool check_index_structure(const exprt &index_expr)
{
  return (can_cast_expr<index_exprt>(index_expr) ||
          can_cast_expr<byte_extract_exprt>(index_expr)) &&
         index_expr.operands().size() == 2 &&
         check_symbol_structure(to_binary_expr(index_expr).op0()) &&
         can_evaluate_to_constant(to_binary_expr(index_expr).op1());
}

bool check_struct_structure(const struct_exprt &expr)
{
  if(!expr.has_operands())
    return false;
  if(const auto sub_struct = expr_try_dynamic_cast<struct_exprt>(expr.op0()))
    check_struct_structure(*sub_struct);
  else if(
    !can_cast_expr<constant_exprt>(expr.op0()) &&
    !can_cast_expr<annotated_pointer_constant_exprt>(expr.op0()))
  {
    return false;
  }
  if(
    expr.operands().size() > 1 && std::any_of(
                                    ++expr.operands().begin(),
                                    expr.operands().end(),
                                    [&](const exprt &operand) {
                                      return operand.id() != ID_constant &&
                                             operand.id() !=
                                               ID_annotated_pointer_constant;
                                    }))
  {
    return false;
  }
  return true;
}

bool check_address_structure(const address_of_exprt &address)
{
  const auto symbol_expr = get_inner_symbol_expr(address);
  return symbol_expr && check_symbol_structure(*symbol_expr);
}

bool check_constant_structure(const constant_exprt &constant_expr)
{
  if(constant_expr.has_operands())
    return false;
  // All value types used in Java must be non-empty except string_typet:
  return !constant_expr.get_value().empty() ||
         constant_expr.type() == string_typet();
}

static bool check_annotated_pointer_constant_structure(
  const annotated_pointer_constant_exprt &constant_expr)
{
  const auto &operand = skip_typecast(constant_expr.symbolic_pointer());
  return can_cast_expr<constant_exprt>(operand) ||
         can_cast_expr<address_of_exprt>(operand) ||
         can_cast_expr<plus_exprt>(operand);
}

static void check_lhs_assumptions(
  const exprt &lhs,
  const namespacet &ns,
  const validation_modet vm)
{
  DATA_CHECK_WITH_DIAGNOSTICS(
    vm,
    valid_lhs_expr_high_level(lhs),
    "LHS",
    lhs.pretty(),
    "Unsupported expression.");
  // check member lhs structure
  if(const auto member = expr_try_dynamic_cast<member_exprt>(lhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_member_structure(*member),
      "LHS",
      lhs.pretty(),
      "Expecting a member with nested symbol operand.");
  }
  // check symbol lhs structure
  else if(const auto symbol = expr_try_dynamic_cast<symbol_exprt>(lhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_symbol_structure(*symbol),
      "LHS",
      lhs.pretty(),
      "Expecting a symbol with non-empty identifier.");
  }
  // check index lhs structure
  else if(const auto index = expr_try_dynamic_cast<index_exprt>(lhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_index_structure(*index),
      "LHS",
      lhs.pretty(),
      "Expecting an index expression with a symbol array and constant or "
      "symbol index value.");
  }
  // check byte extract lhs structure
  else if(const auto byte = expr_try_dynamic_cast<byte_extract_exprt>(lhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_index_structure(*byte),
      "LHS",
      lhs.pretty(),
      "Expecting a byte extract expression with a symbol array and constant or "
      "symbol index value.");
  }
  else
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      false,
      "LHS",
      lhs.pretty(),
      "Expression does not meet any trace assumptions.");
  }
}

static void check_rhs_assumptions(
  const exprt &rhs,
  const namespacet &ns,
  const validation_modet vm)
{
  DATA_CHECK_WITH_DIAGNOSTICS(
    vm,
    valid_rhs_expr_high_level(rhs),
    "RHS",
    rhs.pretty(),
    "Unsupported expression.");
  // check address_of rhs structure (String only)
  if(const auto address = expr_try_dynamic_cast<address_of_exprt>(rhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_address_structure(*address),
      "RHS",
      rhs.pretty(),
      "Expecting an address of with nested symbol.");
  }
  // check symbol rhs structure (String only)
  else if(const auto symbol_expr = expr_try_dynamic_cast<symbol_exprt>(rhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_symbol_structure(*symbol_expr),
      "RHS",
      rhs.pretty(),
      "Expecting a symbol with non-empty identifier.");
  }
  // check struct rhs structure
  else if(const auto struct_expr = expr_try_dynamic_cast<struct_exprt>(rhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_struct_structure(*struct_expr),
      "RHS",
      rhs.pretty(),
      "Expecting all non-base class operands to be constants.");
  }
  // check array rhs structure
  else if(can_cast_expr<array_exprt>(rhs))
  {
    // seems no check is required.
  }
  // check array rhs structure
  else if(can_cast_expr<array_list_exprt>(rhs))
  {
    // seems no check is required.
  }
  // check constant rhs structure
  else if(const auto constant_expr = expr_try_dynamic_cast<constant_exprt>(rhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_constant_structure(*constant_expr),
      "RHS",
      rhs.pretty(),
      "Expecting a constant expression to have no operands and a non-empty "
      "value.");
  }
  // check pointer constant rhs structure
  else if(
    const auto constant_expr =
      expr_try_dynamic_cast<annotated_pointer_constant_exprt>(rhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      check_annotated_pointer_constant_structure(*constant_expr),
      "RHS",
      rhs.pretty(),
      "Expecting the operand of an annotated  pointer constant expression "
      "to be a constant, address_of, or plus expression.");
  }
  // check byte extract rhs structure
  else if(const auto byte = expr_try_dynamic_cast<byte_extract_exprt>(rhs))
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      byte->operands().size() == 2,
      "RHS",
      rhs.pretty(),
      "Expecting a byte extract with two operands.");
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      can_cast_expr<constant_exprt>(simplify_expr(byte->op(), ns)),
      "RHS",
      rhs.pretty(),
      "Expecting a byte extract with constant value.");
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      can_cast_expr<constant_exprt>(simplify_expr(byte->offset(), ns)),
      "RHS",
      rhs.pretty(),
      "Expecting a byte extract with constant index.");
  }
  else
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      false,
      "RHS",
      rhs.pretty(),
      "Expression does not meet any trace assumptions.");
  }
}

static void check_step_assumptions(
  const goto_trace_stept &step,
  const namespacet &ns,
  const validation_modet vm)
{
  if(!step.is_assignment() && !step.is_decl())
    return;
  check_lhs_assumptions(skip_typecast(step.full_lhs), ns, vm);
  check_rhs_assumptions(skip_typecast(step.full_lhs_value), ns, vm);
}

void check_trace_assumptions(
  const goto_tracet &trace,
  const namespacet &ns,
  const messaget &log,
  const bool run_check,
  const validation_modet vm)
{
  if(!run_check)
    return;
  for(const auto &step : trace.steps)
    check_step_assumptions(step, ns, vm);
  log.status() << "Trace validation successful" << messaget::eom;
}

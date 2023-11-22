/*******************************************************************\

Module: Evaluate if an expression is consistent with examples

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Evaluate if an expression is consistent with examples

#include "cegis_evaluator.h"

#include <util/arith_tools.h>
#include <util/format_expr.h>

bool cegis_evaluatort::evaluate()
{
  auto is_inconsistent = false;
  // Check if checked_expr is consistent with all examples.
  for(const auto &cex : cexs)
  {
    // checked_expr is inconsistent with a positive example if its evaluation
    // false.
    is_inconsistent =
      is_inconsistent || !evaluate_rec_bool(checked_expr, cex, 1);
    // checked_expr is inconsistent with a negative example if its evaluation
    // false.
    is_inconsistent =
      is_inconsistent || evaluate_rec_bool(checked_expr, cex, 0);
  }
  return !is_inconsistent;
}

bool cegis_evaluatort::evaluate_rec_bool(
  const exprt &expr,
  const cext &cex,
  const bool is_positive)
{
  const auto id = expr.id();
  // eval(AND op1 op2) :=
  // eval(op1) && eval(op2)
  if(id == ID_and)
  {
    bool result = true;
    for(auto &op : expr.operands())
    {
      result = result && evaluate_rec_bool(op, cex, is_positive);
    }
    return result;
  }

  // eval(OR op1 op2) :=
  // eval(op1) || eval(op2)
  if(id == ID_or)
  {
    bool result = false;
    for(auto &op : expr.operands())
    {
      result = result || evaluate_rec_bool(op, cex, is_positive);
    }
    return result;
  }

  // eval(IMPLIES op1 op2) :=
  // eval(op1) => eval(op2)
  if(id == ID_implies)
  {
    return !evaluate_rec_bool(expr.operands()[0], cex, is_positive) ||
           evaluate_rec_bool(expr.operands()[1], cex, is_positive);
  }

  // eval(NOT op) :=
  // !eval(op)
  if(id == ID_not)
  {
    return !evaluate_rec_bool(expr.operands()[0], cex, is_positive);
  }

  // eval(EQUAL op1 op2) :=
  // eval(op1) == eval(op2)
  if(id == ID_equal)
  {
    return evaluate_rec_int(expr.operands()[0], cex, is_positive) ==
           evaluate_rec_int(expr.operands()[1], cex, is_positive);
  }

  // eval(NOTEQUAL op1 op2) :=
  // eval(op1) != eval(op2)
  if(id == ID_notequal)
  {
    return evaluate_rec_int(expr.operands()[0], cex, is_positive) !=
           evaluate_rec_int(expr.operands()[1], cex, is_positive);
  }

  // eval(LE op1 op2) :=
  // eval(op1) <= eval(op2)
  if(id == ID_le)
  {
    return evaluate_rec_int(expr.operands()[0], cex, is_positive) <=
           evaluate_rec_int(expr.operands()[1], cex, is_positive);
  }

  // eval(LT op1 op2) :=
  // eval(op1) < eval(op2)
  if(id == ID_lt)
  {
    return evaluate_rec_int(expr.operands()[0], cex, is_positive) <
           evaluate_rec_int(expr.operands()[1], cex, is_positive);
  }

  // eval(GE op1 op2) :=
  // eval(op1) >= eval(op2)
  if(id == ID_ge)
  {
    return evaluate_rec_int(expr.operands()[0], cex, is_positive) >=
           evaluate_rec_int(expr.operands()[1], cex, is_positive);
  }

  // eval(GT op1 op2) :=
  // eval(op1) > eval(op2)
  if(id == ID_gt)
  {
    return evaluate_rec_int(expr.operands()[0], cex, is_positive) >
           evaluate_rec_int(expr.operands()[1], cex, is_positive);
  }

  // eval(CONST op) :=
  // op
  if(id == ID_constant)
  {
    if(expr == true_exprt())
    {
      return true;
    }
    else if(expr == false_exprt())
    {
      return false;
    }
    UNREACHABLE_BECAUSE(
      "Boolean constant must be either true or false: " + expr.pretty());
  }

  UNREACHABLE_BECAUSE(
    "Found a unsupported boolean operator during quick filtering: " +
    expr.id_string());
}

mp_integer cegis_evaluatort::evaluate_rec_int(
  const exprt &expr,
  const cext &cex,
  const bool is_positive)
{
  const auto id = expr.id();
  mp_integer result;

  // For symbol expression, we look up their values from the example.
  // There are three cases:
  // 1. is_positive == true
  //    We evaluate the expression on the positive examples, which is the
  //    valuation of loop_entry(v). Note that the loop invariants must hold
  //    for loop_entry valuations as the base case. So we look up the values
  //    in the loop_entry set
  // 2. is_positive == false, expr in the havoced set
  //    We evaluate the expression on the negative examples---the havoced set.
  // 3. is_positive == false, expr not in havoced set
  //    The valuations of expr in the havoced iteration is the same as
  //    in the loop entry. So we look up the values from loop_entry set.
  if(id == ID_symbol)
  {
    if(
      cex.havoced_values.find(expr) != cex.havoced_values.end() && !is_positive)
    {
      // Use havoc values if they exists and we are evaluating on
      // the negative example---is_positive is false.
      result = cex.havoced_values.at(expr);
    }
    else if(cex.loop_entry_values.find(expr) != cex.loop_entry_values.end())
    {
      result = cex.loop_entry_values.at(expr);
    }
    else
    {
      UNREACHABLE_BECAUSE(
        "Variable not found in the havoced set or the un-havoced set: " +
        expr.pretty());
    }

    // Typecast `result` to the type of `expr`.
    auto tmp_expr = from_integer(result, expr.type());
    to_integer(tmp_expr, result);
    return result;
  }

  // For loop_entry expression, we look up their values from loop_entry set.
  if(id == ID_loop_entry)
  {
    if(
      cex.loop_entry_values.find(expr.operands()[0]) !=
      cex.loop_entry_values.end())
    {
      result = cex.loop_entry_values.at(expr.operands()[0]);
    }
    else
    {
      UNREACHABLE_BECAUSE(
        "Variable not found in the havoced set or the un-havoced set: " +
        expr.pretty());
    }

    // Typecast `result` to the type of `expr`.
    auto tmp_expr = from_integer(result, expr.type());
    to_integer(tmp_expr, result);
    return result;
  }

  // Evaluate the underlying expression and then typecast the result.
  if(id == ID_typecast)
  {
    // Typecast `result` to the type of `expr`.
    result = evaluate_rec_int(expr.operands()[0], cex, is_positive);
    auto tmp_expr = from_integer(result, expr.type());
    to_integer(tmp_expr, result);
    return result;
  }

  // For object_size expression, look up the size of the underlying pointer in
  // the example `cex`.
  if(id == ID_object_size)
  {
    if(cex.object_sizes.find(expr.operands()[0]) != cex.object_sizes.end())
    {
      result = cex.object_sizes.at(expr.operands()[0]);
    }
    else
    {
      UNREACHABLE_BECAUSE(
        "Variable not found in the object size set: " + expr.pretty());
    }

    // Typecast `result` to the type of `expr`.
    auto tmp_expr = from_integer(result, expr.type());
    to_integer(tmp_expr, result);
    return result;
  }

  // For pointer_offset expression, look up the offset of the underlying
  // pointer in the example `cex`.
  // A pointer offset expression can be of form
  // pointer_offset(p)
  // or
  // pointer_offset(loop_entry(p))
  // for some pointer p.
  // For the first case, we look up the offset in havoced
  // offset set. Note that if the pointer is not in the havoced set or
  // is_positive is set, we look up in loop_entry_offset set instead.
  // For the second case, we look up the offset in the loop_entry_offset set.
  if(id == ID_pointer_offset)
  {
    if(expr.operands()[0].id() != ID_loop_entry)
    {
      // If the expression is pointer_offset(p), look up the offset in the
      // havoced offset set.
      if(
        cex.havoced_pointer_offsets.find(expr.operands()[0]) !=
          cex.havoced_pointer_offsets.end() &&
        !is_positive)
      {
        // Use havoc values only if we are evaluating the expression against
        // the negative example---is_positive is false.
        result = cex.havoced_pointer_offsets.at(expr.operands()[0]);
      }
      else if(
        cex.loop_entry_offsets.find(expr.operands()[0]) !=
        cex.loop_entry_offsets.end())
      {
        // The pointer is not havoced. So look up the offset in the loop-entry
        // set instead.
        result = cex.loop_entry_offsets.at(expr.operands()[0]);
      }
      else
      {
        UNREACHABLE_BECAUSE(
          "Variable not found in the offset set: " + expr.pretty());
      }
    }
    else
    {
      // If the expression is pointer_offset(loop_entry(p)), look up the
      // offset in the offset-of-loop-entry-set.
      if(
        cex.loop_entry_offsets.find(expr.operands()[0].operands()[0]) !=
        cex.loop_entry_offsets.end())
      {
        result = cex.loop_entry_offsets.at(expr.operands()[0].operands()[0]);
      }
      else
      {
        UNREACHABLE_BECAUSE(
          "Variable not found in the offset set: " + expr.pretty());
      }
    }

    // Typecast `result` to the type of `expr`.
    auto tmp_expr = from_integer(result, expr.type());
    to_integer(tmp_expr, result);
    return result;
  }

  // For a constant expression, return its evaluation.
  if(id == ID_constant)
  {
    to_integer(to_constant_expr(expr), result);
    return result;
  }

  // For a plus expression, return the sum of the evaluations of two operands.
  if(id == ID_plus)
  {
    result = evaluate_rec_int(expr.operands()[0], cex, is_positive) +
             evaluate_rec_int(expr.operands()[1], cex, is_positive);

    // Typecast `result` to the type of `expr`.
    auto tmp_expr = from_integer(result, expr.type());
    to_integer(tmp_expr, result);
    return result;
  }

  // For a minus expression, return difference of evaluations of two operands.
  if(id == ID_minus)
  {
    result = evaluate_rec_int(expr.operands()[0], cex, is_positive) -
             evaluate_rec_int(expr.operands()[1], cex, is_positive);

    // Typecast `result` to the type of `expr`.
    auto tmp_expr = from_integer(result, expr.type());
    to_integer(tmp_expr, result);
    return result;
  }

  UNREACHABLE_BECAUSE(
    "Found a unsupported operator during quick filtering: " + expr.id_string());
}

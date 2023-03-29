/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_root_object.h"

#include <util/byte_operators.h>
#include <util/cprover_prefix.h>
#include <util/expr.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <goto-programs/pointer_arithmetic.h>

/// Recursively computes a set of root object expressions for \p expr.
static void
root_objects_rec(const exprt &expr, std::unordered_set<exprt, irep_hash> &dest)
{
  if(expr.id() == ID_symbol)
  {
    dest.insert(expr);
  }
  else if(expr.id() == ID_index)
  {
    root_objects_rec(to_index_expr(expr).array(), dest);
  }
  else if(expr.id() == ID_member)
  {
    const typet &type = to_member_expr(expr).struct_op().type();
    DATA_INVARIANT(
      type.id() == ID_struct || type.id() == ID_struct_tag ||
        type.id() == ID_union || type.id() == ID_union_tag,
      "unexpected assignment to member of '" + type.id_string() + "'");
    root_objects_rec(to_member_expr(expr).compound(), dest);
  }
  else if(expr.id() == ID_if)
  {
    root_objects_rec(to_if_expr(expr).true_case(), dest);
    root_objects_rec(to_if_expr(expr).false_case(), dest);
  }
  else if(expr.id() == ID_typecast)
  {
    root_objects_rec(to_typecast_expr(expr).op(), dest);
  }
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    root_objects_rec(to_byte_extract_expr(expr).op(), dest);
  }
  else if(expr.id() == ID_complex_real)
  {
    root_objects_rec(to_complex_real_expr(expr).op(), dest);
  }
  else if(expr.id() == ID_complex_imag)
  {
    root_objects_rec(to_complex_imag_expr(expr).op(), dest);
  }
  else if(const auto &deref = expr_try_dynamic_cast<dereference_exprt>(expr))
  {
    // normalise the dereferenced pointer into `pointer + offset`, extract
    // pointer expression and try some simplifications
    const exprt &pointer = pointer_arithmetict(deref->pointer()).pointer;
    const source_locationt source_location = expr.source_location();
    if(const auto &if_expr = expr_try_dynamic_cast<if_exprt>(pointer))
    {
      // split on disjunctions
      // *(c ? true_case : false_case) => rec(*true_case); rec(*false_case)
      dereference_exprt if_true(if_expr->true_case());
      if_true.add_source_location() = source_location;
      root_objects_rec(if_true, dest);
      dereference_exprt if_false(if_expr->false_case());
      if_false.add_source_location() = source_location;
      root_objects_rec(if_false, dest);
    }
    else if(
      const auto &address_of_expr =
        expr_try_dynamic_cast<address_of_exprt>(pointer))
    {
      // *(&object + offset) => rec(object)
      root_objects_rec(skip_typecast(address_of_expr->object()), dest);
    }
    else
    {
      // simplify *(pointer + offset) to *pointer and stop here
      dereference_exprt deref(pointer);
      deref.add_source_location() = source_location;
      dest.insert(deref);
    }
  }
  else
  {
    // Stop here for anything else.
    dest.insert(expr);
  }
}

/// Translates object slice expressions found in assigns clause targets to
/// dereference expressions so that root objects can be computed.
static exprt slice_op_to_deref(const exprt &expr)
{
  if(
    const auto &function_call_expr =
      expr_try_dynamic_cast<side_effect_expr_function_callt>(expr))
  {
    auto function_expr = function_call_expr->function();
    INVARIANT(
      function_expr.id() == ID_symbol,
      "no function pointer calls in loop assigns clause targets");
    auto function_id = to_symbol_expr(function_expr).get_identifier();
    INVARIANT(
      function_id == CPROVER_PREFIX "assignable" ||
        function_id == CPROVER_PREFIX "object_whole" ||
        function_id == CPROVER_PREFIX "object_from" ||
        function_id == CPROVER_PREFIX "object_upto",
      "can only handle built-in function calls in assigns clause targets");
    return dereference_exprt(
      skip_typecast(function_call_expr->arguments().at(0)));
  }
  else
  {
    return expr;
  }
}

std::unordered_set<exprt, irep_hash> dfcc_root_objects(const exprt &expr)
{
  std::unordered_set<exprt, irep_hash> result;
  root_objects_rec(slice_op_to_deref(expr), result);
  return result;
}

/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_base_idents.h"

#include <util/byte_operators.h>
#include <util/cprover_prefix.h>
#include <util/expr.h>
#include <util/std_code.h>

#include <iostream>

/// \brief Skips over a typecast expression
static const exprt &skip_typecast(const exprt &expr)
{
  if(expr.id() == ID_typecast)
  {
    return skip_typecast(expr.operands().at(0));
  }
  return expr;
}

/// \brief Tries to match an expression of the form `arr[idx]`
/// where arr has an array type and returns `arr` if successfull
static optionalt<exprt> match_index_of_array(const exprt &expr)
{
  const exprt &skipped = skip_typecast(expr);
  if(skipped.id() == ID_index)
  {
    const exprt &op0 = skipped.operands().at(0);
    if(op0.type().id() == ID_array)
    {
      return op0;
    }
  }
  return nullopt;
}

/// \brief Tries to match \p expr with pattern `arr[idx]` modulo typecasts
/// where arr has an array type and returns `arr` if successfull
static optionalt<exprt> match_address_of(const exprt &expr)
{
  const exprt &skipped = skip_typecast(expr);
  if(skipped.id() == ID_address_of)
  {
    return skipped.operands().at(0);
  }
  return nullopt;
}

/// \brief Tries to match \p expr with pattern `&arr[idx]` modulo typecasts
/// where `arr` has an array type and returns `arr` if successfull.
static optionalt<exprt> match_adrress_of_array_index(const exprt &expr)
{
  const exprt &skipped = skip_typecast(expr);
  if(skipped.id() == ID_address_of)
  {
    const exprt &subexpr = skipped.operands().at(0);
    return match_index_of_array(subexpr);
  }
  return nullopt;
}

/// \brief Tries to match \p expr with pattern `*(&subexpr)` modulo typecasts
/// `subexpr` if successfull
static optionalt<exprt> match_dereference_of_address_of(const exprt &expr)
{
  const exprt &skipped = skip_typecast(expr);
  if(skipped.id() == ID_dereference)
  {
    const exprt &subexpr = skipped.operands().at(0);
    return match_address_of(subexpr);
  }
  return nullopt;
}

static bool dfcc_base_idents_rec(const exprt &expr, std::set<irep_idt> &dest)
{
  // The case-splitting on the lhs copied from symex_assignt::assign_rec
  // and should cover all cases that symex knows about assignments.
  if(expr.id() == ID_symbol)
  {
    dest.insert(to_symbol_expr(expr).get_identifier());
    return true;
  }
  else if(expr.id() == ID_index)
  {
    return dfcc_base_idents_rec(to_index_expr(expr).array(), dest);
  }
  else if(expr.id() == ID_member)
  {
    const typet &type = to_member_expr(expr).struct_op().type();
    if(
      type.id() == ID_struct || type.id() == ID_struct_tag ||
      type.id() == ID_union || type.id() == ID_union_tag)
    {
      return dfcc_base_idents_rec(to_member_expr(expr).compound(), dest);
    }
    else
    {
      throw unsupported_operation_exceptiont(
        "unexpected assignment to member of '" + type.id_string() + "'");
    }
  }
  else if(expr.id() == ID_if)
  {
    return dfcc_base_idents_rec(to_if_expr(expr).true_case(), dest) &&
           dfcc_base_idents_rec(to_if_expr(expr).false_case(), dest);
  }
  else if(expr.id() == ID_typecast)
  {
    return dfcc_base_idents_rec(to_typecast_expr(expr).op(), dest);
  }
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    return dfcc_base_idents_rec(to_byte_extract_expr(expr).op(), dest);
  }
  else if(expr.id() == ID_complex_real)
  {
    return dfcc_base_idents_rec(to_complex_real_expr(expr).op(), dest);
  }
  else if(expr.id() == ID_complex_imag)
  {
    return dfcc_base_idents_rec(to_complex_imag_expr(expr).op(), dest);
  }
  else
  {
    if(can_cast_expr<side_effect_expr_function_callt>(expr))
    {
      auto function_call_expr = to_side_effect_expr_function_call(expr);
      auto function_expr = function_call_expr.function();
      if(function_expr.id() == ID_symbol)
      {
        auto function_id = to_symbol_expr(function_expr).get_identifier();
        INVARIANT(
          function_id == CPROVER_PREFIX "assignable" ||
            function_id == CPROVER_PREFIX "object_whole" ||
            function_id == CPROVER_PREFIX "object_from" ||
            function_id == CPROVER_PREFIX "object_upto" ||
            function_id == CPROVER_PREFIX "typed_target",
          "only built-in function calls allowed in assigns clause targets for "
          "loops");
        return dfcc_base_idents_rec(function_call_expr.arguments().at(0), dest);
      }
    }
    // for these two patterns we can actually locate the base identifier
    auto subexpr = match_adrress_of_array_index(expr);
    if(subexpr.has_value())
    {
      return dfcc_base_idents_rec(subexpr.value(), dest);
    }
    subexpr = match_dereference_of_address_of(expr);
    if(subexpr.has_value())
    {
      return dfcc_base_idents_rec(subexpr.value(), dest);
    }
    // but otherwise we bail
    return false;
  }
}

optionalt<std::set<irep_idt>> dfcc_base_idents(const exprt &expr)
{
  std::set<irep_idt> dest;
  if(dfcc_base_idents_rec(expr, dest))
  {
    return dest;
  }
  else
  {
    return {};
  }
}

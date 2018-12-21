/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific expressions
/// If the expression is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#include "require_expr.h"

#include <testing-utils/catch.hpp>
#include <util/arith_tools.h>
#include <util/std_code.h>

/// Verify a given exprt is an index_exprt with a a constant value equal to the
/// expected value
/// \param expr: The expression.
/// \param expected_index: The constant value that should be the index.
/// \return The expr cast to an index_exprt
index_exprt require_expr::require_index(const exprt &expr, int expected_index)
{
  REQUIRE(expr.id()==ID_index);
  const index_exprt &index_expr=to_index_expr(expr);
  REQUIRE(index_expr.index().id()==ID_constant);
  const mp_integer index_integer_value =
    numeric_cast_v<mp_integer>(index_expr.index());
  REQUIRE(index_integer_value==expected_index);

  return index_expr;
}

/// Verify a given exprt is an index_exprt with a nil value as its index
/// \param expr: The expression.
/// \return The expr cast to an index_exprt
index_exprt require_expr::require_top_index(const exprt &expr)
{
  REQUIRE(expr.id()==ID_index);
  const index_exprt &index_expr=to_index_expr(expr);
  REQUIRE(index_expr.index().id()==ID_nil);
  return index_expr;
}

/// Verify a given exprt is an member_exprt with a component name equal to the
/// component_identifier
/// \param expr: The expression.
/// \param component_identifier: The name of the component that should be being
///   accessed.
/// \return The expr cast to a member_exprt.
member_exprt require_expr::require_member(
  const exprt &expr, const irep_idt &component_identifier)
{
  REQUIRE(expr.id()==ID_member);
  const member_exprt &member_expr=to_member_expr(expr);
  REQUIRE(member_expr.get_component_name()==component_identifier);
  return member_expr;
}

/// Verify a given exprt is an symbol_exprt with a identifier name equal to the
/// symbol_name.
/// \param expr: The expression.
/// \param symbol_name: The intended identifier of the symbol
/// \return The expr cast to a symbol_exprt
symbol_exprt require_expr::require_symbol(
  const exprt &expr, const irep_idt &symbol_name)
{
  const symbol_exprt &symbol_expr = require_symbol(expr);
  REQUIRE(symbol_expr.get_identifier()==symbol_name);
  return symbol_expr;
}

/// Verify a given exprt is a symbol_exprt.
/// \param expr: The expression.
/// \return The expr cast to a symbol_exprt
symbol_exprt require_expr::require_symbol(const exprt &expr)
{
  REQUIRE(expr.id() == ID_symbol);
  return to_symbol_expr(expr);
}

/// Verify a given exprt is a typecast_expr.
/// \param expr: The expression.
/// \return The expr cast to a typecast_exprt
typecast_exprt require_expr::require_typecast(const exprt &expr)
{
  REQUIRE(expr.id() == ID_typecast);
  return to_typecast_expr(expr);
}

/// Verify a given exprt is a side_effect_exprt with appropriate statement.
/// \param expr: The expression.
/// \param side_effect_statement: The kind of side effect that is required
/// \return The expr cast to a side_effect_exprt
side_effect_exprt require_expr::require_side_effect_expr(
  const exprt &expr,
  const irep_idt &side_effect_statement)
{
  REQUIRE(expr.id() == ID_side_effect);
  const side_effect_exprt &side_effect_expr = to_side_effect_expr(expr);
  REQUIRE(side_effect_expr.get_statement() == side_effect_statement);
  return side_effect_expr;
}

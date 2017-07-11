/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific expressions
/// If the expression is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#include "require_expr.h"

#include <catch.hpp>
#include <util/arith_tools.h>

/// Verify a given exprt is an index_exprt with a a constant value equal to the
/// expected value
/// \param expr: The expression.
/// \param expected_index: The constant value that should be the index.
/// \return The expr cast to an index_exprt
index_exprt require_exprt::require_index(const exprt &expr, int expected_index)
{
  REQUIRE(expr.id()==ID_index);
  const index_exprt &index_expr=to_index_expr(expr);
  REQUIRE(index_expr.index().id()==ID_constant);
  const constant_exprt &index_value=to_constant_expr(index_expr.index());
  mp_integer index_integer_value;
  to_integer(index_value, index_integer_value);
  REQUIRE(index_integer_value==expected_index);

  return index_expr;
}

/// Verify a given exprt is an index_exprt with a nil value as its index
/// \param expr: The expression.
/// \return The expr cast to an index_exprt
index_exprt require_exprt::require_top_index(const exprt &expr)
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
member_exprt require_exprt::require_member(
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
symbol_exprt require_exprt::require_symbol(
  const exprt &expr, const irep_idt &symbol_name)
{
  REQUIRE(expr.id()==ID_symbol);
  const symbol_exprt &symbol_expr=to_symbol_expr(expr);
  REQUIRE(symbol_expr.get_identifier()==symbol_name);
  return symbol_expr;
}

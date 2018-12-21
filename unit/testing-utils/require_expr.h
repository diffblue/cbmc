/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific expressions
/// If the expression is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#ifndef CPROVER_TESTING_UTILS_REQUIRE_EXPR_H
#define CPROVER_TESTING_UTILS_REQUIRE_EXPR_H

#include <util/std_expr.h>
#include <util/std_code.h>

// NOLINTNEXTLINE(readability/namespace)
namespace require_expr
{
  index_exprt require_index(const exprt &expr, int expected_index);
  index_exprt require_top_index(const exprt &expr);

  member_exprt require_member(
    const exprt &expr, const irep_idt &component_identifier);

  symbol_exprt require_symbol(
    const exprt &expr, const irep_idt &symbol_name);

  symbol_exprt require_symbol(const exprt &expr);

  typecast_exprt require_typecast(const exprt &expr);

  side_effect_exprt require_side_effect_expr(
    const exprt &expr,
    const irep_idt &side_effect_statement);
}

#endif // CPROVER_TESTING_UTILS_REQUIRE_EXPR_H

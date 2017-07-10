/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific expressions
/// If the expression is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#ifndef CPROVER_SRC_EXPR_REQUIRE_EXPR_H
#define CPROVER_SRC_EXPR_REQUIRE_EXPR_H

#include <util/std_expr.h>

namespace require_exprt
{
  index_exprt require_index(const exprt &expr, int expected_index);
  index_exprt require_top_index(const exprt &expr);

  member_exprt require_member(
    const exprt &expr, const irep_idt &component_identifier);

  symbol_exprt require_symbol(
    const exprt &expr, const irep_idt &symbol_name);
};

#endif // CPROVER_SRC_EXPR_REQUIRE_EXPR_H

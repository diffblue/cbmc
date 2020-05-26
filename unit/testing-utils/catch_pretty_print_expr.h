/*******************************************************************\

Module: Pretty print exprts in Catch assertions

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_CATCH_PRETTY_PRINT_EXPR_H
#define CPROVER_TESTING_UTILS_CATCH_PRETTY_PRINT_EXPR_H

// this file is expected to be included from `use_catch.hpp`,
// this include is only here to make editor syntax highlighting
// work better
#include <catch/catch.hpp>

#include <ansi-c/expr2c.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

namespace Catch // NOLINT
{
template <>
struct StringMaker<exprt> // NOLINT
{
  static std::string convert(const exprt &expr)
  {
    // expr2c doesn’t capture everything that’s contained
    // within an expr, but it’s fairly compact.
    // expr.pretty() could also work and is more precise,
    // but leads to very large output multiple lines which
    // makes it hard to see differences.
    return expr2c(expr, namespacet{symbol_tablet{}});
  }
};
} // namespace Catch

#endif // CPROVER_TESTING_UTILS_CATCH_PRETTY_PRINT_EXPR_H

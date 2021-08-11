/*******************************************************************\

Module: Utilities for building havoc code for expressions.

Author: Saswat Padhi, saspadhi@amazon.com

Date: July 2021

\*******************************************************************/

/// \file
/// Utilities for building havoc code for expressions

#ifndef CPROVER_GOTO_INSTRUMENT_HAVOC_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_HAVOC_UTILS_H

#include <set>

#include <goto-programs/goto_program.h>

#include <util/expr_util.h>

typedef std::set<exprt> modifiest;

class havoc_utils_is_constantt : public is_constantt
{
public:
  explicit havoc_utils_is_constantt(const modifiest &mod) : modifies(mod)
  {
  }

  bool is_constant(const exprt &expr) const override
  {
    // Besides the "usual" constants (checked in is_constantt::is_constant),
    // we also treat unmodified symbols as constants
    if(expr.id() == ID_symbol && modifies.find(expr) == modifies.end())
      return true;

    return is_constantt::is_constant(expr);
  }

protected:
  const modifiest &modifies;
};

void append_havoc_code(
  const source_locationt source_location,
  const modifiest &modifies,
  goto_programt &dest);

void append_object_havoc_code_for_expr(
  const source_locationt source_location,
  const exprt &expr,
  goto_programt &dest);

void append_scalar_havoc_code_for_expr(
  const source_locationt source_location,
  const exprt &expr,
  goto_programt &dest);

#endif // CPROVER_GOTO_INSTRUMENT_HAVOC_UTILS_H

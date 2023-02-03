/*******************************************************************\

Module: Utilities for building havoc code for expressions.

Author: Saswat Padhi, saspadhi@amazon.com

Date: July 2021

\*******************************************************************/

/// \file
/// Utilities for building havoc code for expressions

#include "havoc_utils.h"

#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <goto-programs/goto_program.h>

void havoc_utilst::append_full_havoc_code(
  const source_locationt location,
  goto_programt &dest) const
{
  for(const auto &expr : assigns)
    append_havoc_code_for_expr(location, expr, dest);
}

void havoc_utilst::append_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  append_scalar_havoc_code_for_expr(location, expr, dest);
}

void havoc_utilst::append_object_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  codet havoc(ID_havoc_object);
  havoc.add_source_location() = location;
  havoc.add_to_operands(expr);
  dest.add(goto_programt::make_other(havoc, location));
}

void havoc_utilst::append_scalar_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  side_effect_expr_nondett rhs(expr.type(), location);
  dest.add(goto_programt::make_assignment(
    code_assignt{expr, std::move(rhs), location}, location));
}

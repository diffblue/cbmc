/*******************************************************************\

Module: Utilities for building havoc code for expressions.

Author: Saswat Padhi, saspadhi@amazon.com

Date: July 2021

\*******************************************************************/

/// \file
/// Utilities for building havoc code for expressions

#include "havoc_utils.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>

void append_safe_havoc_code_for_expr(
  const source_locationt source_location,
  const exprt &expr,
  goto_programt &dest,
  const std::function<void()> &havoc_code_impl)
{
  goto_programt skip_program;
  const auto skip_target =
    skip_program.add(goto_programt::make_skip(source_location));

  // for deref expressions, check for validity of underlying pointer,
  // and skip havocing if invalid (to avoid spurious pointer deref errors)
  if(expr.id() == ID_dereference)
  {
    const auto condition = not_exprt(w_ok_exprt(
      to_dereference_expr(expr).pointer(),
      from_integer(0, unsigned_int_type())));
    dest.add(goto_programt::make_goto(skip_target, condition, source_location));
  }

  havoc_code_impl();

  // for deref expressions, add the final skip target
  if(expr.id() == ID_dereference)
    dest.destructive_append(skip_program);
}

void append_object_havoc_code_for_expr(
  const source_locationt source_location,
  const exprt &expr,
  goto_programt &dest)
{
  append_safe_havoc_code_for_expr(source_location, expr, dest, [&]() {
    codet havoc(ID_havoc_object);
    havoc.add_source_location() = source_location;
    havoc.add_to_operands(expr);
    dest.add(goto_programt::make_other(havoc, source_location));
  });
}

void append_scalar_havoc_code_for_expr(
  const source_locationt source_location,
  const exprt &expr,
  goto_programt &dest)
{
  append_safe_havoc_code_for_expr(source_location, expr, dest, [&]() {
    side_effect_expr_nondett rhs(expr.type(), source_location);
    goto_programt::targett t = dest.add(
      goto_programt::make_assignment(expr, std::move(rhs), source_location));
    t->code_nonconst().add_source_location() = source_location;
  });
}

void append_havoc_code(
  const source_locationt source_location,
  const modifiest &modifies,
  goto_programt &dest)
{
  havoc_utils_is_constantt is_constant(modifies);
  for(const auto &expr : modifies)
  {
    if(expr.id() == ID_index || expr.id() == ID_dereference)
    {
      address_of_exprt address_of_expr(expr);
      if(!is_constant(address_of_expr))
      {
        append_object_havoc_code_for_expr(
          source_location, address_of_expr, dest);
        continue;
      }
    }

    append_scalar_havoc_code_for_expr(source_location, expr, dest);
  }
}

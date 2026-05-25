/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/simplify_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

/// Replace symbol expressions that refer to constant variables with their
/// compile-time values, enabling constant folding in static_assert.
static void
propagate_constants(exprt &expr, const symbol_table_baset &symbol_table)
{
  if(expr.id() == ID_symbol)
  {
    const symbolt *s =
      symbol_table.lookup(to_symbol_expr(expr).get_identifier());
    if(s != nullptr && s->type.get_bool(ID_C_constant) && s->value.is_not_nil())
    {
      expr = s->value;
      return;
    }
  }

  for(auto &op : expr.operands())
    propagate_constants(op, symbol_table);
}

void cpp_typecheckt::convert(cpp_static_assertt &cpp_static_assert)
{
  typecheck_expr(cpp_static_assert.op0());
  typecheck_expr(cpp_static_assert.op1());

  implicit_typecast_bool(cpp_static_assert.op0());

  propagate_constants(cpp_static_assert.op0(), symbol_table);

  simplify(cpp_static_assert.op0(), *this);

  // If the expression cannot be reduced to a constant (e.g., it depends
  // on a template parameter or an unevaluated symbol), skip the check.
  if(!cpp_static_assert.op0().is_constant())
    return;

  if(cpp_static_assert.op0() == false_exprt())
  {
    // failed
    error().source_location=cpp_static_assert.source_location();
    error() << "static assertion failed";
    if(cpp_static_assert.op1().id()==ID_string_constant)
      error() << ": " << to_string_constant(cpp_static_assert.op1()).value();
    error() << eom;
    throw 0;
  }
}

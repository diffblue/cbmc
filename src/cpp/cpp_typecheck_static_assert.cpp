/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/string_constant.h>

void cpp_typecheckt::convert(cpp_static_assertt &cpp_static_assert)
{
  typecheck_expr(cpp_static_assert.op0());
  typecheck_expr(cpp_static_assert.op1());

  implicit_typecast_bool(cpp_static_assert.op0());
  make_constant(cpp_static_assert.op0());

  if(cpp_static_assert.op0().is_false())
  {
    // failed
    error().source_location=cpp_static_assert.source_location();
    error() << "static assertion failed";
    if(cpp_static_assert.op1().id()==ID_string_constant)
      error() << ": "
              << to_string_constant(cpp_static_assert.op1()).get_value();
    error() << eom;
    throw 0;
  }
}

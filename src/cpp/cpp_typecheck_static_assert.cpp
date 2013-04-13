/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/std_types.h>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert(cpp_static_assertt &cpp_static_assert)
{
  typecheck_expr(cpp_static_assert.op0());
  typecheck_expr(cpp_static_assert.op1());

  cpp_static_assert.op0().make_typecast(bool_typet());
  make_constant(cpp_static_assert.op0());

  if(cpp_static_assert.op0().is_true())
  {
    // ok
  }
  else if(cpp_static_assert.op0().is_false())
  {
    // failed
    err_location(cpp_static_assert);
    str << "static assertion failed: ";
    throw 0;
  }
  else
  {
    // not true or false
    err_location(cpp_static_assert);
    str << "static assertion is not constant";
    throw 0;
  }
}

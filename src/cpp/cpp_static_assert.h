/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_STATIC_ASSERT_H
#define CPROVER_CPP_CPP_STATIC_ASSERT_H

#include <util/std_expr.h>

class cpp_static_assertt : public binary_exprt
{
public:
  cpp_static_assertt() : binary_exprt(ID_cpp_static_assert)
  {
  }

  exprt &cond()
  {
    return op0();
  }

  const exprt &cond() const
  {
    return op0();
  }

  const exprt &description() const
  {
    return op1();
  }

  exprt &description()
  {
    return op1();
  }
};

#endif // CPROVER_CPP_CPP_STATIC_ASSERT_H

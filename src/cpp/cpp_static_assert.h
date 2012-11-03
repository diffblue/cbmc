/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_STATIC_ASSERT_H
#define CPROVER_CPP_STATIC_ASSERT_H

#include <expr.h>

class cpp_static_assertt:public exprt
{
public:
  cpp_static_assertt():exprt(ID_cpp_static_assert)
  {
    operands().resize(2);
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

#endif

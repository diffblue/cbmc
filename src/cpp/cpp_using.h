/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_USING_H
#define CPROVER_CPP_CPP_USING_H

#include "cpp_name.h"

class cpp_usingt:public irept
{
public:
  cpp_usingt():irept(ID_cpp_using)
  {
  }

  cpp_namet &name()
  {
    return (cpp_namet &)add(ID_name);
  }

  const cpp_namet &name() const
  {
    return (const cpp_namet &)find(ID_name);
  }

  bool get_namespace() const
  {
    return get_bool(ID_namespace);
  }

  void set_namespace(bool value)
  {
    set(ID_namespace, value);
  }
};

#endif // CPROVER_CPP_CPP_USING_H

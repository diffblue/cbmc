/*******************************************************************\

 Module: Java Bytecode Language Conversion

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#ifndef CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H
#define CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).

#include <util/std_types.h>

class namespacet;

class select_pointer_typet
{
public:
  explicit select_pointer_typet(const namespacet &ns):ns(ns)
  {}

  pointer_typet operator()(const pointer_typet &pointer_type) const;
private:
  bool is_abstract_type(const pointer_typet &pointer_type) const;

  const namespacet &ns;
};

#endif // CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

/*******************************************************************\

Module: Java Bytecode Language Conversion

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Select a subclass of the provided type, picking the alphabetically first

#ifndef CPROVER_JAVA_BYTECODE_GET_CONCRETE_CLASS_ALPHABETICALLY_H
#define CPROVER_JAVA_BYTECODE_GET_CONCRETE_CLASS_ALPHABETICALLY_H

#include <util/std_types.h>

class namespacet;

class get_concrete_class_alphabeticallyt
{
public:
  explicit get_concrete_class_alphabeticallyt(const namespacet &ns):ns(ns)
  {}

  pointer_typet operator()(const pointer_typet &pointer_type);

private:
  const namespacet &ns;
  class_typet select_concrete_type(const class_typet &abstract_type);
};

#endif // CPROVER_JAVA_BYTECODE_GET_CONCRETE_CLASS_ALPHABETICALLY_H

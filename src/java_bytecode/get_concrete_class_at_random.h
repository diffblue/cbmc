/*******************************************************************\

Module: Java Bytecode Language Conversion

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Java Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_GET_CONCRETE_CLASS_AT_RANDOM_H
#define CPROVER_JAVA_BYTECODE_GET_CONCRETE_CLASS_AT_RANDOM_H

#include <util/std_types.h>

class namespacet;

class get_concrete_class_at_randomt
{
public:
  explicit get_concrete_class_at_randomt (const namespacet &ns):ns(ns)
  {}

  typet operator()(const pointer_typet &pointer_type);

private:
  const namespacet& ns;
  class_typet select_concrete_type(const class_typet &abstract_type);
};

#endif // CPROVER_JAVA_BYTECODE_GET_CONCRETE_CLASS_AT_RANDOM_H

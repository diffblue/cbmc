/*******************************************************************\

 Module: Java Bytecode Language Conversion

 Author: Diffblue Ltd.

\*******************************************************************/
#ifndef CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H
#define CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).

#include <util/std_types.h>
#include <stack>
#include "java_types.h"

typedef std::unordered_map<irep_idt, std::stack<reference_typet>, irep_id_hash>
  generic_parameter_specialization_mapt;

class namespacet;

class select_pointer_typet
{
public:
  virtual ~select_pointer_typet() = default;
  virtual pointer_typet convert_pointer_type(
    const pointer_typet &pointer_type,
    const generic_parameter_specialization_mapt
      &generic_parameter_specialization_map,
    const namespacet &ns) const;

  pointer_typet specialize_generics(
    const pointer_typet &pointer_type,
    const generic_parameter_specialization_mapt
      &generic_parameter_specialization_map) const;
};

#endif // CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

/*******************************************************************\

 Module: Java Bytecode Language Conversion

 Author: Diffblue Ltd.

\*******************************************************************/
#ifndef CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H
#define CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).
#include <vector>

#include "java_types.h"
#include <util/optional.h>
#include <util/std_types.h>

typedef std::unordered_map<irep_idt, std::vector<reference_typet>>
  generic_parameter_specialization_mapt;
typedef std::set<irep_idt> generic_parameter_recursion_trackingt;

class namespacet;

class select_pointer_typet
{
  optionalt<pointer_typet> get_recursively_instantiated_type(
    const irep_idt &,
    const generic_parameter_specialization_mapt &,
    generic_parameter_recursion_trackingt &,
    const size_t) const;
  optionalt<pointer_typet> get_recursively_instantiated_type(
    const irep_idt &parameter_name,
    const generic_parameter_specialization_mapt &visited) const;

public:
  virtual ~select_pointer_typet() = default;
  virtual pointer_typet convert_pointer_type(
    const pointer_typet &pointer_type,
    const generic_parameter_specialization_mapt
      &generic_parameter_specialization_map,
    const namespacet &ns) const;

  virtual std::set<symbol_typet> get_parameter_alternative_types(
    const irep_idt &function_name,
    const irep_idt &parameter_name,
    const namespacet &ns) const;

  pointer_typet specialize_generics(
    const pointer_typet &pointer_type,
    const generic_parameter_specialization_mapt
      &generic_parameter_specialization_map,
    generic_parameter_recursion_trackingt &visited) const;
};

#endif // CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

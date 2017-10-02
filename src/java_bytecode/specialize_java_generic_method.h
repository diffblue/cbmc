/*******************************************************************\

Module: Generate Java Generic Method - Instantiate a generic method
        with concrete type information.

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_SPECIALIZE_JAVA_GENERIC_METHOD_H
#define CPROVER_JAVA_BYTECODE_SPECIALIZE_JAVA_GENERIC_METHOD_H

#include <util/message.h>
#include <util/symbol_table.h>
#include <util/std_types.h>
#include <java_bytecode/java_types.h>
#include "generate_java_generic_type.h"

/// An exception that is raised when specialization fails.
class unsupported_java_method_specialization_exceptiont:public std::logic_error
{
public:
  explicit unsupported_java_method_specialization_exceptiont(std::string type):
    std::logic_error("Unsupported method specialisation: "+type){}
};

class specialize_java_generic_methodt
{
public:
  typedef std::initializer_list
    <std::pair<const irep_idt, const symbol_typet>>
      type_variable_instantiationst;

  typedef std::unordered_map
    <const irep_idt, const symbol_typet, irep_id_hash>
      type_variable_instantiation_mapt;

  specialize_java_generic_methodt(
    message_handlert &message_handler);

  const symbolt& operator()(
    const symbolt &generic_method,
    const type_variable_instantiationst &concrete_types,
    symbol_tablet &symbol_table) const;

  void instantiate_generic_types(
    typet &generic_type,
    const type_variable_instantiation_mapt &concrete_type_map,
    symbol_tablet &symbol_table) const;

  void instantiate_java_generic_parameter(
    java_generic_parametert &generic_parameter,
    const type_variable_instantiation_mapt &concrete_types,
    const symbol_tablet &symbol_table) const;

  void instantiate_java_generic_type(
    java_generic_typet &generic_type,
    const type_variable_instantiation_mapt &concrete_types) const;

private:
  static const std::string instantiation_decoration(
    type_variable_instantiationst concrete_types);

  static void decorate_identifier(
    irept &expr,
    const irep_idt &identifier,
    const irep_idt &pattern,
    const irep_idt &decoration);

  generate_java_generic_typet instantiate_generic_type;
};


#endif // CPROVER_JAVA_BYTECODE_SPECIALIZE_JAVA_GENERIC_METHOD_H

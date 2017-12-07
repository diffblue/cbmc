/*******************************************************************\

 Module: Generate Java Generic Type - Instantiate a generic class with
         concrete type information.

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#ifndef CPROVER_JAVA_BYTECODE_GENERATE_JAVA_GENERIC_TYPE_H
#define CPROVER_JAVA_BYTECODE_GENERATE_JAVA_GENERIC_TYPE_H

#include <util/message.h>
#include <util/symbol_table.h>
#include <util/std_types.h>
#include <java_bytecode/java_types.h>
#include <functional>
#include "generic_arguments_name_builder.h"

class generate_java_generic_typet
{
public:
  explicit generate_java_generic_typet(message_handlert &message_handler);

  symbolt operator()(
    const java_generic_typet &existing_generic_type,
    symbol_tablet &symbol_table) const;
private:
  std::string build_generic_name(
    const java_generic_typet &existing_generic_type,
    const java_class_typet &original_class,
    const generic_arguments_name_buildert::name_printert &argument_name_printer)
    const;

  typet substitute_type(
    const typet &parameter_type,
    const java_class_typet &replacement_type,
    const java_generic_typet &generic_reference) const;

  type_symbolt build_symbol_from_specialised_class(
    const java_class_typet &specialised_class) const;

  message_handlert &message_handler;
};

#endif // CPROVER_JAVA_BYTECODE_GENERATE_JAVA_GENERIC_TYPE_H

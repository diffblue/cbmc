/*******************************************************************\

 Module: MODULE NAME

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#ifndef GENERATE_JAVA_GENERIC_TYPE_H
#define GENERATE_JAVA_GENERIC_TYPE_H

#include <util/message.h>
#include <util/symbol_table.h>
#include <util/std_types.h>
#include <java_bytecode/java_types.h>

class generate_java_generic_typet
{
public:
  generate_java_generic_typet(
    symbol_tablet &symbol_table,
    message_handlert &message_handler);

  symbolt operator()(
    const java_type_with_generic_typet &existing_generic_type);
private:
  irep_idt build_generic_tag(
    const java_type_with_generic_typet &existing_generic_type,
    const java_class_typet &original_class);

  symbol_tablet &symbol_table;

  message_handlert &message_handler;

};

#endif // GENERATE_JAVA_GENERIC_TYPE_H

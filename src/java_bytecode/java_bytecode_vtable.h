/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_VTABLE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_VTABLE_H

#include <util/std_types.h>

void create_vtable_pointer(
  class symbolt &class_symbol);

void create_vtable_symbol(
  symbol_tablet &symbol_table,
  const class symbolt &class_symbol);

bool has_vtable_info(
  const symbol_tablet &symbol_table,
  const symbolt &class_symbol);

exprt make_vtable_function(
  const exprt &function,
  const exprt &this_obj);

void set_virtual_name(
  class_typet::methodt &method);

bool java_bytecode_vtable(
  symbol_tablet &symbol_table,
  const std::string &module);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_VTABLE_H

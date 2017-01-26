/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H
#define CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H

#include <util/message.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

exprt object_factory(
  const typet &type,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table,
  size_t max_nondet_array_length,
  const source_locationt &,
  message_handlert &message_handler);

void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const source_locationt &,
  bool skip_classid,
  bool create_dynamic_objects,
  bool assume_non_null,
  message_handlert &message_handler,
  size_t max_nondet_array_length=5);


exprt get_nondet_bool(const typet &);

symbolt &new_tmp_symbol(
  symbol_tablet &symbol_table,
  const std::string &prefix="tmp_object_factory");

#endif // CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H

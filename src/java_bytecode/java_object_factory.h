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

enum update_in_placet
{
  NO_UPDATE_IN_PLACE,
  MAY_UPDATE_IN_PLACE,
  MUST_UPDATE_IN_PLACE
};

void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const source_locationt &,
  bool skip_classid,
  bool create_dynamic_objects,
  bool assume_non_null,
  message_handlert &message_handler,
  size_t max_nondet_array_length,
  update_in_placet update_in_place=NO_UPDATE_IN_PLACE);


exprt get_nondet_bool(const typet &);

symbolt &new_tmp_symbol(
  symbol_tablet &symbol_table,
  const source_locationt &,
  const typet &,
  const std::string &prefix="tmp_object_factory");

#endif // CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H

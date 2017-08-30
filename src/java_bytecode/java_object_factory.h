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
  const irep_idt base_name,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table,
  size_t max_nondet_array_length,
  const source_locationt &);

#endif // CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H

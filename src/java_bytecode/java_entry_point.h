/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H
#define CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H

#include <util/irep.h>
#include <util/symbol.h>

#define JAVA_ENTRY_POINT_RETURN_SYMBOL "return'"

bool java_entry_point(
  class symbol_tablet &symbol_table,
  const irep_idt &main_class,
  class message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  size_t max_nondet_array_length);

typedef struct
{
  symbolt main_function;
  bool error_found;
  bool stop_convert;
} main_function_resultt;

main_function_resultt get_main_symbol(
  symbol_tablet &symbol_table,
  const irep_idt &main_class,
  message_handlert &,
  bool allow_no_body=false);

#endif // CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H

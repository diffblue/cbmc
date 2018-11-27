/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H
#define CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H

#include "java_bytecode_language.h"
#include "select_pointer_type.h"

#include <util/irep.h>
#include <util/symbol.h>

#define JAVA_ENTRY_POINT_RETURN_SYMBOL "return'"
#define JAVA_ENTRY_POINT_EXCEPTION_SYMBOL "uncaught_exception'"

bool java_entry_point(
  class symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  class message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  bool string_refinement_enabled);

struct main_function_resultt
{
  enum statust
  {
    Success,
    Error,
    NotFound
  } status;
  symbolt main_function;

  // Implicit conversion doesn't lose information and allows return of status
  // NOLINTNEXTLINE(runtime/explicit)
  main_function_resultt(statust status) : status(status)
  {
  }

  // Implicit conversion doesn't lose information and allows return of symbol
  // NOLINTNEXTLINE(runtime/explicit)
  main_function_resultt(const symbolt &main_function)
    : status(Success), main_function(main_function)
  {
  }

  bool is_success() const
  {
    return status == Success;
  }
  bool is_error() const
  {
    return status == Error;
  }
};

irep_idt get_java_class_literal_initializer_signature();

/// Figures out the entry point of the code to verify
main_function_resultt get_main_symbol(
  const symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  message_handlert &);

bool generate_java_start_function(
  const symbolt &symbol,
  class symbol_table_baset &symbol_table,
  class message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector);

#endif // CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H

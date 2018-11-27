/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H
#define CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H

#include <ansi-c/c_object_factory_parameters.h>
#include <util/message.h>
#include <util/symbol_table.h>

bool ansi_c_entry_point(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  const c_object_factory_parameterst &object_factory_parameters);

bool generate_ansi_c_start_function(
  const symbolt &symbol,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  const c_object_factory_parameterst &object_factory_parameters);

#endif // CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H

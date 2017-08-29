/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H
#define CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/std_code.h>

bool ansi_c_entry_point(
  symbol_tablet &symbol_table,
  const std::string &standard_main,
  message_handlert &message_handler,
  bool wrap_entry_point);

code_whilet wrap_entry_point_in_while(
  code_function_callt &call_main);

#endif // CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H

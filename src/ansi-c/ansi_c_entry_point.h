/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H
#define CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H

#include <util/symbol_table.h>
#include <util/message.h>

bool ansi_c_entry_point(
  symbol_tablet &symbol_table,
  const std::string &standard_main,
  message_handlert &message_handler);

#endif // CPROVER_ANSI_C_ANSI_C_ENTRY_POINT_H

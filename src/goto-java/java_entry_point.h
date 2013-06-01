/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_ENTRY_POINT_H
#define CPROVER_JAVA_ENTRY_POINT_H

#include <util/symbol_table.h>
#include <util/message.h>

bool java_entry_point(
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

#endif

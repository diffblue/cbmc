/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LINKING_ENTRY_POINT_H
#define CPROVER_LINKING_ENTRY_POINT_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/source_location.h>

bool entry_point(
  symbol_tablet &symbol_table,
  const std::string &standard_main,
  message_handlert &message_handler);

bool static_lifetime_init(
  symbol_tablet &symbol_table,
  const source_locationt &source_location,
  message_handlert &message_handler);

#endif

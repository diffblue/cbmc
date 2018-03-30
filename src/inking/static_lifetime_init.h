/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_LINKING_STATIC_LIFETIME_INIT_H
#define CPROVER_LINKING_STATIC_LIFETIME_INIT_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/source_location.h>
#include <util/cprover_prefix.h>

bool static_lifetime_init(
  symbol_tablet &symbol_table,
  const source_locationt &source_location,
  message_handlert &message_handler);

#define INITIALIZE_FUNCTION CPROVER_PREFIX "initialize"

#endif // CPROVER_LINKING_STATIC_LIFETIME_INIT_H

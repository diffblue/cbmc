/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_LINKING_STATIC_LIFETIME_INIT_H
#define CPROVER_LINKING_STATIC_LIFETIME_INIT_H

#include <util/cprover_prefix.h>

class message_handlert;
class source_locationt;
class symbol_tablet;

void static_lifetime_init(
  symbol_tablet &symbol_table,
  const source_locationt &source_location);

#define INITIALIZE_FUNCTION CPROVER_PREFIX "initialize"

#endif // CPROVER_LINKING_STATIC_LIFETIME_INIT_H

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_LINKING_STATIC_LIFETIME_INIT_H
#define CPROVER_LINKING_STATIC_LIFETIME_INIT_H

#include <util/cprover_prefix.h>

class goto_modelt;
class message_handlert;
class source_locationt;
class symbol_table_baset;

void static_lifetime_init(
  symbol_table_baset &symbol_table,
  const source_locationt &source_location);

#define INITIALIZE_FUNCTION CPROVER_PREFIX "initialize"

/// Regenerates the CPROVER_INITIALIZE function, which initializes all
/// non-function symbols of the goto model that have static lifetime. It is an
/// error if CPROVER_INITIALIZE was not present beforehand.
void recreate_initialize_function(goto_modelt &, message_handlert &);

#endif // CPROVER_LINKING_STATIC_LIFETIME_INIT_H

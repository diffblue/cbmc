/*******************************************************************\

Module: Remove symbols that are internal only

Author: Daniel Kroening

\*******************************************************************/

#ifndef CPROVER_LINKING_REMOVE_INTERNAL_SYMBOLS_H
#define CPROVER_LINKING_REMOVE_INTERNAL_SYMBOLS_H

#include <util/source_location.h>

class message_handlert;
class symbol_tablet;

typedef hash_map_cont<irep_idt, source_locationt, irep_id_hash>
  include_mapt;

void remove_internal_symbols(
  symbol_tablet &symbol_table,
  const include_mapt &include_map,
  message_handlert &message_handler);

#endif

/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_ADD_FAILED_SYMBOLS_H
#define CPROVER_POINTER_ANALYSIS_ADD_FAILED_SYMBOLS_H

#include <util/irep.h>

class symbol_tablet;
class exprt;
class namespacet;
class symbol_exprt;

void add_failed_symbols(symbol_tablet &symbol_table);

irep_idt failed_symbol_id(const irep_idt &identifier);

exprt get_failed_symbol(
  const symbol_exprt &expr,
  const namespacet &ns);

#endif // CPROVER_POINTER_ANALYSIS_ADD_FAILED_SYMBOLS_H

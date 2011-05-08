/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_FAILED_SYMBOLS_H
#define CPROVER_POINTER_ANALYSIS_FAILED_SYMBOLS_H

#include <context.h>
#include <namespace.h>
#include <std_expr.h>

void add_failed_symbols(contextt &context);

irep_idt failed_symbol_id(const irep_idt &identifier);

exprt get_failed_symbol(
  const symbol_exprt &expr,
  const namespacet &ns);

#endif

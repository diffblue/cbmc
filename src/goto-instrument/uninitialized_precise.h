/*******************************************************************\

Module: Precise uninitialized variable check using shadow memory

Author: Kiro

\*******************************************************************/

/// \file
/// Instruments a goto model with shadow-memory-based uninitialized
/// variable checks.  Uses __CPROVER_field_decl_local / set_field /
/// get_field so that symex resolves aliasing and interprocedural
/// writes precisely.

#ifndef CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_PRECISE_H
#define CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_PRECISE_H

class goto_modelt;
class message_handlert;

void add_uninitialized_checks_precise(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_PRECISE_H

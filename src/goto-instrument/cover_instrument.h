/*******************************************************************\

Module: Coverage Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_INSTRUMENT_H
#define CPROVER_GOTO_INSTRUMENT_COVER_INSTRUMENT_H

#include <goto-programs/goto_model.h>

class cover_basic_blockst;
class goal_filterst;

void cover_instrument_location(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_basic_blockst &basic_blocks,
  const goal_filterst &goal_filters);

void cover_instrument_branch(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_basic_blockst &basic_blocks);

void cover_instrument_decision(
  const namespacet &ns,
  goto_programt &goto_program,
  goto_programt::targett &i_it);

void cover_instrument_condition(
  const namespacet &ns,
  goto_programt &goto_program,
  goto_programt::targett &i_it);

void cover_instrument_mcdc(
  const namespacet &ns,
  goto_programt &goto_program,
  goto_programt::targett &i_it);

void cover_instrument_path(goto_programt::targett &i_it);

void cover_instrument_assertion(goto_programt::targett &i_it);

void cover_instrument_cover(const namespacet &ns, goto_programt::targett &i_it);

void cover_instrument_end_of_function(
  const irep_idt &function,
  goto_programt &goto_program);

#endif // CPROVER_GOTO_INSTRUMENT_COVER_INSTRUMENT_H

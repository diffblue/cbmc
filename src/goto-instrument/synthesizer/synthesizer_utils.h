/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_SYNTHESIZER_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_SYNTHESIZER_UTILS_H

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/loop_ids.h>

#include <analyses/loop_analysis.h>
#include <goto-instrument/loop_utils.h>

class messaget;

typedef std::map<loop_idt, exprt> invariant_mapt;

/// Find the goto instruction of `loop` that jumps to `loop_head`
goto_programt::targett get_loop_end_from_loop_head_and_content_mutable(
  const goto_programt::targett &loop_head,
  const loop_templatet<goto_programt::targett> &loop);
goto_programt::const_targett get_loop_end_from_loop_head_and_content(
  const goto_programt::const_targett &loop_head,
  const loop_templatet<goto_programt::const_targett> &loop);

/// Return loop head if `finding_head` is true,
/// Otherwise return loop end.
goto_programt::targett get_loop_head_or_end(
  const unsigned int loop_number,
  goto_functiont &function,
  bool finding_head);

/// Find and return the last instruction of the natural loop with
/// `loop_number` in `function`. loop_end -> loop_head
goto_programt::targett
get_loop_end(const unsigned int loop_number, goto_functiont &function);

/// Find and return the first instruction of the natural loop with
/// `loop_number` in `function`. loop_end -> loop_head
goto_programt::targett
get_loop_head(const unsigned int loop_number, goto_functiont &function);

/// Annotate the invariants in `invariant_map` to their corresponding
/// loops. Corresponding loops are specified by keys of `invariant_map`
void annotate_invariants(
  const invariant_mapt &invariant_map,
  goto_modelt &goto_model,
  messaget &log);

#endif // CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_SYNTHESIZER_UTILS_H

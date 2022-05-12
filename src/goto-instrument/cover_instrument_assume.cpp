/// \file cover_instrument_assume.cpp
/// Author: Diffblue Ltd.
/// Coverage Instrumentation for ASSUME instructions.

#include "cover_instrument.h"

#include "ansi-c/expr2c.h"
#include "goto-programs/goto_program.h"
#include "util/std_expr.h"
#include <util/namespace.h>

/// Instrument program to check coverage of assume statements.
/// \param function_id The name of the function under instrumentation.
/// \param goto_program The goto-program (function under instrumentation).
/// \param i_it The current instruction (instruction under instrumentation).
/// \param make_assertion The assertion generator function.
void cover_assume_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_blocks_baset &,
  const assertion_factoryt &make_assertion) const
{
  if(i_it->is_assume())
  {
    const auto location = i_it->source_location();
    const auto assume_condition =
      expr2c(i_it->condition(), namespacet{symbol_tablet()});
    const auto comment_before =
      "assert(false) before assume(" + assume_condition + ")";
    const auto comment_after =
      "assert(false) after assume(" + assume_condition + ")";

    const auto assert_before = make_assertion(false_exprt{}, location);
    goto_programt::targett t = goto_program.insert_before(i_it, assert_before);
    initialize_source_location(t, comment_before, function_id);

    const auto assert_after = make_assertion(false_exprt{}, location);
    t = goto_program.insert_after(i_it, assert_after);
    initialize_source_location(t, comment_after, function_id);
  }
  // Otherwise, skip existing assertions.
  else if(i_it->is_assert())
  {
    const auto location = i_it->source_location();
    // Filter based on if assertion was added by us as part of instrumentation.
    if(location.get_property_class() != "coverage")
    {
      i_it->turn_into_skip();
    }
  }
}

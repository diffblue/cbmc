/*******************************************************************\

Module: Instrument Given Invariants

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Instrument Given Invariants

#include "instrument_given_invariants.h"

#include <goto-programs/goto_model.h>

void instrument_given_invariants(goto_functionst::function_mapt::value_type &f)
{
  auto &body = f.second.body;

  for(auto it = body.instructions.begin(); it != body.instructions.end(); it++)
  {
    // annotated invariants -- these are stuck to the condition
    // of the (backwards) goto
    if(it->is_backwards_goto())
    {
      const auto &invariants = static_cast<const exprt &>(
        it->condition().find(ID_C_spec_loop_invariant));

      for(const auto &invariant : invariants.operands())
      {
        auto source_location = invariant.source_location(); // copy
        source_location.set_property_class("invariant");
        source_location.set_comment("loop invariant");

        auto assertion =
          goto_programt::make_assertion(invariant, source_location);

        body.insert_before_swap(it->get_target(), assertion);
      }
    }
  }
}

void instrument_given_invariants(goto_modelt &goto_model)
{
  for(auto &f : goto_model.goto_functions.function_map)
    instrument_given_invariants(f);
}

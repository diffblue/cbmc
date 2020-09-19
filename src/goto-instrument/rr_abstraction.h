/*******************************************************************\

Module: Rr_abstraction

Author: Lefan Zhang, lefanz@amazon.com
        Murali Talupur talupur@amazon.com

\*******************************************************************/

/// \file
/// Replication Reducing Abstraction (RRA) for getting unbounded proofs.
/// Similar to abstractions used in protocol verification, RRA feature
/// reduces large data structures to small sizes by tracking a few
/// locations precisely and conservatively over-approximating other
/// locations. For instance, an array might be abstracted by tracking just
/// one location precisely. All locations before it are lumped into one
/// abstract location and similarly, all locations after it. This "shape" can
/// be viewed as being similar to the regex "*c*".
/// To use this feature user specifies a json file with arrays/strings
/// to be abstracted along with the locations to keep precise, relation
/// between them, helper functions for abstracting the other locations. 
/// See regression/abstraction folder for some examples.
/// This resulting program over-approximates the actual program and
/// since the array/string has a small size the loop unwinding in CBMC
/// can be small while still giving us an unbounded proof.

#ifndef CPROVER_GOTO_INSTRUMENT_RR_ABSTRACTION_H
#define CPROVER_GOTO_INSTRUMENT_RR_ABSTRACTION_H

#include <util/expr.h>
#include <util/json.h>

#include <goto-programs/goto_model.h>
#include <util/options.h>
#include <util/ui_message.h>

#include "rr_abstraction_spect.h"

class rr_abstractiont
{
public:
  // link abst functions to goto programs
  static void link_abst_functions(
    goto_modelt &goto_model,
    const rr_abstraction_spect &abst_spec,
    ui_message_handlert &msg_handler,
    const optionst &options);

  // abstract goto programs
  static void
  abstract_goto_program(goto_modelt &goto_model, rr_abstraction_spect &abst_spec);
};

#endif // CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H

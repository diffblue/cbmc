/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_SYMEX_VERIFY_EXTRACT_COUNTEREXAMPLE_H
#define CPROVER_CEGIS_INVARIANT_SYMEX_VERIFY_EXTRACT_COUNTEREXAMPLE_H

#include <goto-programs/goto_program.h>

/**
 * @brief Counterexample type for this CEGIS component.
 *
 * @details Counterexamples give a set of values used for the state variables.
 */
typedef std::map<const irep_idt, exprt> counterexamplet;

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param trace
 * @param quantifiers
 */
void invariant_extract_counterexample(counterexamplet &result,
    const class goto_tracet &trace, const goto_programt::targetst &quantifiers);

#endif // CPROVER_CEGIS_INVARIANT_SYMEX_VERIFY_EXTRACT_COUNTEREXAMPLE_H

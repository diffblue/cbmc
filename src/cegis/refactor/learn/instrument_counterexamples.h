/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_LEARN_INSTRUMENT_COUNTEREXAMPLES_H
#define CPROVER_CEGIS_REFACTOR_LEARN_INSTRUMENT_COUNTEREXAMPLES_H

#include <cegis/refactor/value/refactor_counterexample.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ces
 */
void instrument_counterexamples(
    class refactor_programt &prog,
    refactor_counterexamplest ces);

#endif // CPROVER_CEGIS_REFACTOR_LEARN_INSTRUMENT_COUNTEREXAMPLES_H

/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_REFACTOR_LEARN_INSTRUMENT_COUNTEREXAMPLES_H_
#define CEGIS_REFACTOR_LEARN_INSTRUMENT_COUNTEREXAMPLES_H_

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

#endif /* CEGIS_REFACTOR_LEARN_INSTRUMENT_COUNTEREXAMPLES_H_ */

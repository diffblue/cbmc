/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_INSERT_COUNTEREXAMPLE_H_
#define CEGIS_JSA_INSERT_COUNTEREXAMPLE_H_

#include <cegis/jsa/value/jsa_counterexample.h>

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param ces
 */
void insert_counterexamples(
    class jsa_programt &program,
    const jsa_counterexamplest &ces);

#endif /* CEGIS_JSA_INSERT_COUNTEREXAMPLE_H_ */

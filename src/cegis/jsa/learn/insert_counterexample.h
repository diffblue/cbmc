/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_LEARN_INSERT_COUNTEREXAMPLE_H
#define CPROVER_CEGIS_JSA_LEARN_INSERT_COUNTEREXAMPLE_H

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

#endif // CPROVER_CEGIS_JSA_LEARN_INSERT_COUNTEREXAMPLE_H

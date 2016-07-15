/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_EXTRACT_COUNTEREXAMPLE_H_
#define CEGIS_JSA_EXTRACT_COUNTEREXAMPLE_H_

#include <cegis/jsa/value/jsa_counterexample.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ce
 * @param trace
 */
void extract(
    const class jsa_programt &prog,
    jsa_counterexamplet &ce,
    const class goto_tracet &trace);

#endif /* CEGIS_JSA_EXTRACT_COUNTEREXAMPLE_H_ */

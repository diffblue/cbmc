/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/value/jsa_solution.h>

#ifndef CEGIS_JSA_CONVERT_SOLUTION_H_
#define CEGIS_JSA_CONVERT_SOLUTION_H_

// TODO: Convert genetic solution to irep / irep to genetic solution

/**
 * @brief
 *
 * @details
 *
 * @param solution
 * @param prog
 * @return
 */
jsa_solutiont convert(
    const class jsa_genetic_solutiont &solution,
    const class jsa_programt &prog);

#endif /* CEGIS_JSA_CONVERT_SOLUTION_H_ */

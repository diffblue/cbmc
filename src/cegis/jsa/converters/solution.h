/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/value/jsa_solution.h>

#ifndef CPROVER_CEGIS_JSA_CONVERTERS_SOLUTION_H
#define CPROVER_CEGIS_JSA_CONVERTERS_SOLUTION_H

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

#endif // CPROVER_CEGIS_JSA_CONVERTERS_SOLUTION_H

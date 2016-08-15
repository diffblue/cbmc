/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_SOLUTION_PRINTER_H_
#define CEGIS_JSA_SOLUTION_PRINTER_H_

#include <util/message.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param program
 * @param solution
 */
void print_jsa_solution(
    messaget::mstreamt &os,
    const class jsa_programt &program,
    const class jsa_solutiont &solution);

#endif /* CEGIS_JSA_SOLUTION_PRINTER_H_ */

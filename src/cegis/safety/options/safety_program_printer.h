/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SAFETY_PROGRAM_PRINTER_H_
#define CEGIS_SAFETY_PROGRAM_PRINTER_H_

#include <util/message.h>

#include <cegis/safety/value/safety_goto_solution.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param program
 * @param solution
 */
void print_safety_program(messaget::mstreamt &os,
    const class safety_programt &program,
    const safety_goto_solutiont &solution);

#endif /* CEGIS_DANGER_PROGRAM_PRINTER_H_ */

/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_OPTIONS_SAFETY_PROGRAM_PRINTER_H
#define CPROVER_CEGIS_SAFETY_OPTIONS_SAFETY_PROGRAM_PRINTER_H

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

#endif // CPROVER_CEGIS_SAFETY_OPTIONS_SAFETY_PROGRAM_PRINTER_H

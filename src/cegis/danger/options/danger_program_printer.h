/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_OPTIONS_DANGER_PROGRAM_PRINTER_H
#define CPROVER_CEGIS_DANGER_OPTIONS_DANGER_PROGRAM_PRINTER_H

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
void print_danger_program(messaget::mstreamt &os,
    const class danger_programt &program,
    const class danger_goto_solutiont &solution);

#endif // CPROVER_CEGIS_DANGER_OPTIONS_DANGER_PROGRAM_PRINTER_H

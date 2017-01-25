/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONTROL_LEARN_PRINT_CONTROL_SOLUTION_H
#define CPROVER_CEGIS_CONTROL_LEARN_PRINT_CONTROL_SOLUTION_H

#include <util/message.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param array
 * @param name
 * @param st
 */
void print_control_array(
    messaget::mstreamt &os,
    const array_exprt &array,
    const char * name,
    const symbol_tablet &st);

#endif // CPROVER_CEGIS_CONTROL_LEARN_PRINT_CONTROL_SOLUTION_H

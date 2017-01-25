/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_LEARN_PRINT_CONTROL_SOLUTION_H_
#define CEGIS_CONTROL_LEARN_PRINT_CONTROL_SOLUTION_H_

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

#endif /* CEGIS_CONTROL_LEARN_PRINT_CONTROL_SOLUTION_H_ */

/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_PROPAGATE_CONTROLLER_SIZES_H_
#define CEGIS_PROPAGATE_CONTROLLER_SIZES_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param ns
 * @param value
 * @param comp
 */
const exprt &get_controller_comp(
    const namespacet &ns,
    const struct_exprt &value,
    const char * const comp);

/**
 * @brief
 *
 * @details
 *
 * @param ns
 * @param value
 *
 * @return
 */
const array_exprt &get_a_controller_comp(
    const namespacet &ns,
    const struct_exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @param ns
 * @param value
 *
 * @return
 */
const array_exprt &get_b_controller_comp(
    const namespacet &ns,
    const struct_exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 */
void propagate_controller_sizes(
    const class symbol_tablet &st,
    class goto_functionst &gf);

/**
 * @brief
 *
 * @details
 *
 * @param body
 */
void remove_solution_assignment(goto_programt &body);

/**
 * @brief
 *
 * @details
 *
 * @param body
 *
 * @return
 */
goto_programt::targett get_solution_assignment(goto_programt &body);

#endif /* CEGIS_PROPAGATE_CONTROLLER_SIZES_H_ */

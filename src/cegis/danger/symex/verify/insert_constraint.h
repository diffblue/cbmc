/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_INSERT_CONSTRAINT_H_
#define CEGIS_DANGER_INSERT_CONSTRAINT_H_

#include <deque>
#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param quantifiers
 * @param program
 */
void danger_insert_constraint(goto_programt::targetst &quantifiers,
    class danger_programt &program);

typedef std::deque<symbol_exprt> constraint_varst;

/**
 * @brief
 *
 * @details
 *
 * @param vars
 * @param program
 */
void get_danger_constraint_vars(constraint_varst &vars,
    const danger_programt &program);

#endif /* CEGIS_DANGER_INSERT_CONSTRAINT_H_ */

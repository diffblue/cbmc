/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_INVARIANT_INSERT_CONSTRAINT_H_
#define CEGIS_INVARIANT_INSERT_CONSTRAINT_H_

#include <deque>
#include <functional>

#include <goto-programs/goto_program.h>

/**
 * @brief Constraint factory function.
 *
 * @details Provides the constraint to test counterexamples against (safety or danger).
 */
typedef std::function<exprt(size_t)> constraint_factoryt;

/**
 * @brief
 *
 * @details
 *
 * @param quantifiers
 * @param program
 * @param constraint_factory
 */
void invariant_insert_constraint(goto_programt::targetst &quantifiers,
    class invariant_programt &program, constraint_factoryt constraint_factory);

#endif /* CEGIS_INVARIANT_INSERT_CONSTRAINT_H_ */

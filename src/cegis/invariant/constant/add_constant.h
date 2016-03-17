/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_ADD_CONSTANT_H_
#define CEGIS_DANGER_ADD_CONSTANT_H_

#include <string>

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param value
 */
void add_danger_constant(class invariant_programt &program,
    const class exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param name
 * @param value
 */
void add_danger_constant(invariant_programt &program, const std::string &name,
    const exprt &value);

#endif /* CEGIS_DANGER_ADD_CONSTANT_H_ */

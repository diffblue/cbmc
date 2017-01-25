/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_CONSTANT_ADD_CONSTANT_H
#define CPROVER_CEGIS_INVARIANT_CONSTANT_ADD_CONSTANT_H

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

#endif // CPROVER_CEGIS_INVARIANT_CONSTANT_ADD_CONSTANT_H

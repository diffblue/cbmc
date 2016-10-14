/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_ADD_CONSTANT_H_
#define CEGIS_ADD_CONSTANT_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param value
 */
void add_cegis_constant(
    class symbol_tablet &st,
    class goto_functionst &gf,
    const class exprt &value,
    goto_programt::targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param name
 * @param value
 * @param pos
 */
void add_cegis_constant(
    class symbol_tablet &st,
    class goto_functionst &gf,
    const std::string &name,
    const exprt &value,
    goto_programt::targett pos);

#endif /* CEGIS_ADD_CONSTANT_H_ */

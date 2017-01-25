/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONSTANT_ADD_CONSTANT_H
#define CPROVER_CEGIS_CONSTANT_ADD_CONSTANT_H

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

#endif // CPROVER_CEGIS_CONSTANT_ADD_CONSTANT_H

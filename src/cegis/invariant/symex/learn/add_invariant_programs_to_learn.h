/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_ADD_INVARIANT_PROGRAMS_TO_LEARN_H
#define CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_ADD_INVARIANT_PROGRAMS_TO_LEARN_H

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param decl
 */
std::string get_prog_var_name(const symbol_tablet &st,
    const goto_programt::targett &decl);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param max_solution_size
 * @param decl
 * @param prog_base_name
 */
void execute_inv_prog(const symbol_tablet &st, goto_functionst &gf,
    size_t max_solution_size, const goto_programt::targett &decl,
    const std::string &prog_base_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param max_solution_size
 * @param decl
 */
void execute_inv_prog(const symbol_tablet &st, goto_functionst &gf,
    size_t max_solution_size, const goto_programt::targett &decl);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param pos
 * @param max_solution_size
 * @param decl
 */
goto_programt::targett add_inv_prog(invariant_programt &prog,
    goto_programt::targett pos, size_t max_solution_size,
    const goto_programt::targett &decl);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 */
goto_programt::targett add_invariant_progs_to_learn(
    class invariant_programt &prog, size_t max_solution_size);

#endif // CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_ADD_INVARIANT_PROGRAMS_TO_LEARN_H

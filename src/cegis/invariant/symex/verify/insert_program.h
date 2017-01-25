/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_SYMEX_VERIFY_INSERT_PROGRAM_H
#define CPROVER_CEGIS_INVARIANT_SYMEX_VERIFY_INSERT_PROGRAM_H

#include <goto-programs/goto_program.h>

typedef std::map<const irep_idt, const irep_idt> replacementst;

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 * @param prog
 */
void insert_program(goto_programt &body, const goto_programt::targett &pos,
    const goto_programt::instructionst &prog);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 * @param prog
 * @param org_name
 * @param new_name
 */
void insert_program(goto_programt &body, const goto_programt::targett &pos,
    const goto_programt::instructionst &prog, const irep_idt &org_name,
    const irep_idt &new_name);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 * @param prog
 * @param replacements
 */
void insert_program(goto_programt &body, goto_programt::targett pos,
    const goto_programt::instructionst &prog, const replacementst &replacements);

#endif // CPROVER_CEGIS_INVARIANT_SYMEX_VERIFY_INSERT_PROGRAM_H

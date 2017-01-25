/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_REPLACE_OPERATORS_H
#define CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_REPLACE_OPERATORS_H

#include <goto-programs/goto_program.h>

typedef std::map<size_t, const irep_idt> invariant_variable_namest;
typedef std::map<const irep_idt, size_t> operand_variable_idst;

/**
 * @brief
 *
 * @details
 *
 * @param names
 * @param ids
 */
void reverse_invariant_var_ids(invariant_variable_namest &names,
    const operand_variable_idst &ids);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param func_name
 * @param first
 * @param last
 * @param names
 * @param rnames
 * @param op0
 * @param op1
 * @param op2
 * @param instr_idx
 */
void replace_ops_in_instr(const symbol_tablet &st, const std::string &func_name,
    const goto_programt::targett &first, const goto_programt::targett &last,
    const invariant_variable_namest &names, const invariant_variable_namest &rnames,
    const size_t op0, const size_t op1, const size_t op2,
    const size_t instr_idx);

#endif // CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_REPLACE_OPERATORS_H

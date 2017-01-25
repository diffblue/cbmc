/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_CONVERTERS_REPLACE_OPERATORS_H
#define CPROVER_CEGIS_JSA_CONVERTERS_REPLACE_OPERATORS_H

#include <goto-programs/goto_program.h>

#include <cegis/jsa/value/jsa_genetic_synthesis.h>

/**
 * @brief
 *
 * @details
 *
 * @param first
 * @param last
 * @param instr
 */
void replace_pred_ops(
    goto_programt::targett first,
    const goto_programt::const_targett &last,
    const __CPROVER_jsa_pred_instructiont &instr);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param first
 * @param last
 * @param instr
 * @param prefix
 */
void replace_query_ops(
    const class symbol_tablet &st,
    goto_programt::targett first,
    const goto_programt::const_targett &last,
    const __CPROVER_jsa_query_instructiont &instr,
    const __CPROVER_jsa_query_instructiont &prefix);

#endif // CPROVER_CEGIS_JSA_CONVERTERS_REPLACE_OPERATORS_H

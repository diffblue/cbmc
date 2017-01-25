/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_CONVERTERS_TRANSLATE_TO_GOTO_PROGRAM_H
#define CPROVER_CEGIS_JSA_CONVERTERS_TRANSLATE_TO_GOTO_PROGRAM_H

#include <goto-programs/goto_program.h>
#include <cegis/jsa/value/jsa_genetic_synthesis.h>

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param prog
 * @param solution
 * @return
 */
void convert(
    goto_programt::instructionst &result,
    const class jsa_programt &prog,
    const std::vector<__CPROVER_jsa_pred_instructiont> &solution);

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param prog
 * @param solution
 */
void convert(
    goto_programt::instructionst &result,
    const jsa_programt &prog,
    const std::vector<__CPROVER_jsa_query_instructiont> &solution);

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param prog
 * @param solution
 */
void convert(
    goto_programt::instructionst &result,
    const jsa_programt &prog,
    const std::vector<__CPROVER_jsa_invariant_instructiont> &solution);

#endif // CPROVER_CEGIS_JSA_CONVERTERS_TRANSLATE_TO_GOTO_PROGRAM_H

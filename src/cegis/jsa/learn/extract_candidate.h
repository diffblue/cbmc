/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_LEARN_EXTRACT_CANDIDATE_H
#define CPROVER_CEGIS_JSA_LEARN_EXTRACT_CANDIDATE_H

#include <cegis/jsa/value/pred_ops.h>

/**
 * @brief
 *
 * @details
 *
 * @param solution
 * @param prog
 * @param trace
 */
void extract_jsa_genetic_candidate(
    class jsa_genetic_solutiont &solution,
    const class jsa_programt &prog,
    const class goto_tracet &trace);

/**
 * @brief
 *
 * @details
 *
 * @param solution
 * @param trace
 * @param const_pred_ops
 * @param pred_ops
 * @param max_size
 */
void extract_jsa_candidate(
    class jsa_solutiont &solution,
    const jsa_programt &prog,
    const goto_tracet &trace,
    const pred_op_idst &pred_ops,
    const pred_op_idst &result_pred_ops,
    const size_t max_size);

#endif // CPROVER_CEGIS_JSA_LEARN_EXTRACT_CANDIDATE_H

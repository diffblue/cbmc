/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_LEARN_INSTRUMENT_PRED_OPS_H
#define CPROVER_CEGIS_JSA_LEARN_INSTRUMENT_PRED_OPS_H

#include <goto-programs/goto_program.h>
#include <cegis/jsa/value/pred_ops.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @return
 */
goto_programt::targetst collect_pred_ops(class jsa_programt &prog);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ops
 * @param op_ids
 * @param const_op_ids
 */
void instrument_pred_ops(
    class jsa_programt &prog,
    const goto_programt::targetst &ops,
    pred_op_idst &op_ids,
    pred_op_idst &const_op_ids);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ops
 */
void instrument_pred_ops(
    class jsa_programt &prog,
    const goto_programt::targetst &ops);

#endif // CPROVER_CEGIS_JSA_LEARN_INSTRUMENT_PRED_OPS_H

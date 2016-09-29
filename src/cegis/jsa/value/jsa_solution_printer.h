/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_SOLUTION_PRINTER_H_
#define CEGIS_JSA_SOLUTION_PRINTER_H_

#include <util/message.h>

#include <cegis/jsa/value/pred_ops.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param program
 * @param solution
 * @param op_ids
 * @param const_op_ids
 */
void print_jsa_solution(
    messaget::mstreamt &os,
    const class jsa_programt &program,
    const class jsa_solutiont &solution,
    const pred_op_idst &op_ids,
    const pred_op_idst &const_op_ids);

#endif /* CEGIS_JSA_SOLUTION_PRINTER_H_ */

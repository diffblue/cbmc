/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_REFACTOR_LEARN_REFACTOR_CANDIDATE_PRINTER_H_
#define CEGIS_REFACTOR_LEARN_REFACTOR_CANDIDATE_PRINTER_H_

#include <util/message.h>

#include <cegis/refactor/value/refactor_solution.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param gf
 * @param candidate
 */
void print_refactor_candidate(
    messaget::mstreamt &os,
    const class symbol_tablet &st,
    const class goto_functionst &gf,
    const refactor_solutiont &candidate);

#endif /* CEGIS_REFACTOR_LEARN_REFACTOR_CANDIDATE_PRINTER_H_ */

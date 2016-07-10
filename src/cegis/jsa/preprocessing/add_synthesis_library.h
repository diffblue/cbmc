/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_ADD_SYNTHESIS_LIBRARY_H_
#define CEGIS_JSA_ADD_SYNTHESIS_LIBRARY_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param max_sz
 * @param pred_op_locations
 */
void add_jsa_library(
    class jsa_programt &prog,
    size_t max_sz,
    const goto_programt::targetst &pred_op_locations);

#endif /* CEGIS_JSA_ADD_SYNTHESIS_LIBRARY_H_ */

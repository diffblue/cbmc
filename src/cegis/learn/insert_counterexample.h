/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_LEARN_INSERT_COUNTEREXAMPLE_H_
#define CEGIS_LEARN_INSERT_COUNTEREXAMPLE_H_

#include <goto-programs/goto_program.h>

#include <cegis/cegis-util/labelled_assignments.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param counterexamples
 * @param ce_locs
 */
void insert_counterexamples(
    class symbol_tablet &st,
    class goto_functionst &gf,
    labelled_counterexamplest counterexamples,
    const goto_programt::targetst &ce_locs);

#endif /* CEGIS_LEARN_INSERT_COUNTEREXAMPLE_H_ */

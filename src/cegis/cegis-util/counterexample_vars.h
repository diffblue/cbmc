/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_COUNTEREXAMPLE_VARS_H_
#define CEGIS_COUNTEREXAMPLE_VARS_H_

#include <functional>

#include <goto-programs/goto_program.h>

#define DEFAULT_MARKER_LABEL_PREFIX CPROVER_PREFIX "_cegis_ce_location_"

/**
 * @brief
 *
 * @details
 *
 * @param locs
 * @param marker_label_prefix
 * @param prog
 * @param is_meta
 */
void collect_counterexample_locations(
    goto_programt::targetst &locs,
    const char * const marker_label_prefix,
    goto_programt &prog,
    const std::function<bool(const goto_programt::targett &target)> is_meta);

/**
 * @brief
 *
 * @details
 *
 * @param locs
 * @param marker_label_prefix
 * @param prog
 */
void collect_counterexample_locations(
    goto_programt::targetst &locs,
    const char * const marker_label_prefix,
    goto_programt &prog);

/**
 * @brief
 *
 * @details
 *
 * @param locs
 * @param prog
 */
void collect_counterexample_locations(
    goto_programt::targetst &locs,
    goto_programt &prog);

#endif /* CEGIS_COUNTEREXAMPLE_VARS_H_ */

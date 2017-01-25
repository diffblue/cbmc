/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_COUNTEREXAMPLE_VARS_H
#define CPROVER_CEGIS_CEGIS_UTIL_COUNTEREXAMPLE_VARS_H

#include <iosfwd>
#include <functional>

#include <goto-programs/goto_program.h>

#include <cegis/cegis-util/labelled_assignments.h>

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
    const std::function<bool(goto_programt::const_targett target)> is_meta);

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

/**
 * @brief
 *
 * @details
 *
 * @param locs
 * @param prog
 * @param is_meta
 */
void collect_counterexample_locations(
    goto_programt::targetst &locs,
    goto_programt &prog,
    const std::function<bool(goto_programt::const_targett target)> is_meta);

/**
 * @brief
 *
 * @details
 *
 * @param locs
 * @param prog
 * @param is_meta
 * @param marker_index_offset
 *
 * @return
 */
size_t collect_counterexample_locations(
    goto_programt::targetst &locs,
    goto_programt &prog,
    const std::function<bool(goto_programt::const_targett target)> is_meta,
    size_t marker_index_offset);

/**
 * @brief
 *
 * @details
 *
 * @param pos
 *
 * @return
 */
bool default_cegis_meta_criterion(const goto_programt::const_targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param trace
 *
 * @return
 */
labelled_assignmentst extract_counterexample(const class goto_tracet &trace);

/**
 * @brief
 *
 * @details
 *
 * @param assignments
 */
void show_assignments(std::ostream &os,
    const labelled_assignmentst &assignments);

/**
 * @brief
 *
 * @details
 *
 * @param pos
 *
 * @return
 */
bool has_counterexample_marker(goto_programt::const_targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param pos
 *
 * @return
 */
const irep_idt &get_counterexample_marker(goto_programt::const_targett pos);

#endif // CPROVER_CEGIS_CEGIS_UTIL_COUNTEREXAMPLE_VARS_H

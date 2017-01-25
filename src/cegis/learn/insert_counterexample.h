/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_LEARN_INSERT_COUNTEREXAMPLE_H
#define CPROVER_CEGIS_LEARN_INSERT_COUNTEREXAMPLE_H

#include <goto-programs/goto_program.h>

#include <cegis/cegis-util/labelled_assignments.h>

/**
 * @brief
 *
 * @details
 */
#define CE_ARRAY_INDEX CPROVER_PREFIX "ce_array_index"

/**
 * @brief
 *
 * @details
 */
typedef std::map<const irep_idt, exprt> zero_valuest;

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param ce_locs
 *
 * @return
 */
zero_valuest get_zero_values(
    const symbol_tablet &st,
    const goto_programt::targetst &ce_locs);

/**
 * @brief
 *
 * @details
 *
 * @param ce_keys
 * @param zv
 * @param ces
 */
void normalise(
    const std::set<irep_idt> &ce_keys,
    const zero_valuest &zv,
    labelled_counterexamplest &ces);

/**
 * @brief
 *
 * @details
 */
typedef std::map<labelled_assignmentst::key_type, array_exprt> array_valuest;

/**
 * @brief
 *
 * @details
 *
 * @param ces
 *
 * @return
 */
array_valuest get_array_values(const labelled_counterexamplest &ces);

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

/**
 * @brief
 *
 * @details
 *
 * @param loc_id
 *
 * @return
 */
std::string get_ce_array_name(const irep_idt &loc_id);

/**
 * @brief
 *
 * @details
 *
 * @param loc_id
 *
 * @return
 */
std::string get_ce_value_index_name(const irep_idt &loc_id);

#endif // CPROVER_CEGIS_LEARN_INSERT_COUNTEREXAMPLE_H

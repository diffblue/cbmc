/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_ADD_COUNTEREXAMPLES_H
#define CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_ADD_COUNTEREXAMPLES_H

#include <deque>
#include <functional>

#include <util/expr.h>

#include <cegis/instrument/literals.h>

/**
 * @brief
 *
 * @details
 */
#define X_CHOICE_PREFIX CEGIS_PREFIX "x_choice_"

/**
 * @brief Counterexample type for this CEGIS component.
 *
 * @details Counterexamples give a set of values used for the state variables.
 */
typedef std::map<const irep_idt, exprt> counterexamplet;
typedef std::deque<counterexamplet> counterexamplest;

/**
 * @brief Constraint factory function.
 *
 * @details Provides the constraint to test counterexamples against (safety or danger).
 */
typedef std::function<exprt(size_t)> constraint_factoryt;

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ces
 * @param use_x0_ce
 */
void invariant_add_learned_counterexamples(class invariant_programt &prog,
    const counterexamplest &ces, constraint_factoryt constraint,
    bool use_x0_ce);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ces
 * @param meta_var_prefix
 */
void invariant_declare_x_choice_arrays(invariant_programt &prog,
    const counterexamplest &ces, const std::string &meta_var_prefix);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ces_size
 * @param use_x0_ce
 *
 * @return
 */
goto_programt::targett invariant_add_ce_loop(invariant_programt &prog,
    const size_t ces_size, const bool use_x0_ce);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param prototype_ce
 * @param num_ces
 * @param meta_var_prefix
 * @param pos
 * @param use_x0_ce
 */
void invariant_assign_ce_values(invariant_programt &prog,
    const counterexamplet &prototype_ce, const size_t num_ces,
    const std::string &meta_var_prefix, const goto_programt::targett pos,
    const bool use_x0_ce);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param constraint
 * @param ce_loop_end
 */
void invariant_add_constraint(invariant_programt &prog,
    const constraint_factoryt constraint,
    const goto_programt::targett &ce_loop_end);

#endif // CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_ADD_COUNTEREXAMPLES_H

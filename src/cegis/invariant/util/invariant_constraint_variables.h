/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_INVARIANT_CONSTRAINT_VARIABLES_H_
#define CEGIS_INVARIANT_CONSTRAINT_VARIABLES_H_

#include <deque>
#include <set>

#include <util/std_expr.h>

/**
 * @brief
 *
 * @details
 */
typedef bool (*symbol_comparatort)(const symbol_exprt &, const symbol_exprt &);

/**
 * @brief
 *
 * @details
 */
typedef std::set<symbol_exprt, symbol_comparatort> invariant_symbol_set;

/**
 * @brief
 *
 * @details
 *
 * @return
 */
invariant_symbol_set create_empty_symbol_set();

/**
 * @brief
 *
 * @details
 *
 * @param vars
 * @param program
 */
void collect_counterexample_variables(invariant_symbol_set &vars,
    const class invariant_programt &program);

/**
 * @brief
 *
 * @details
 */
typedef std::deque<symbol_exprt> constraint_varst;

/**
 * @brief
 *
 * @details
 *
 * @param vars
 * @param program
 */
void get_invariant_constraint_vars(constraint_varst &vars,
    const invariant_programt &program);

#endif /* CEGIS_INVARIANT_CONSTRAINT_VARIABLES_H_ */

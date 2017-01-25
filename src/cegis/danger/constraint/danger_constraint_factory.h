/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_CONSTRAINT_DANGER_CONSTRAINT_FACTORY_H
#define CPROVER_CEGIS_DANGER_CONSTRAINT_DANGER_CONSTRAINT_FACTORY_H

#include <util/std_expr.h>

/**
 * @brief
 *
 * @details
 */
class danger_constraint {
  const bool use_ranking;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param use_ranking
   */
  explicit danger_constraint(bool use_ranking);

  /**
   * @brief
   *
   * @details
   *
   * @param number_of_loops
   */
  exprt operator()(size_t number_of_loops) const;
};

/**
 * @brief
 *
 * @details
 *
 * @param base_name
 *
 * @return
 */
notequal_exprt danger_component_as_bool(const std::string &base_name);

#endif // CPROVER_CEGIS_DANGER_CONSTRAINT_DANGER_CONSTRAINT_FACTORY_H

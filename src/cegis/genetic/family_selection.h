/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_FAMILY_SELECTION_H
#define CPROVER_CEGIS_GENETIC_FAMILY_SELECTION_H

  /**
   * @brief
   *
   * @details
   *
   * @tparam populationt
   */
template<class populationt>
class family_selectiont
{
public:
  /**
   * @brief
   *
   * @details
   */
  typedef std::deque<typename populationt::iterator> individualst;

  /**
   * @brief
   *
   * @details
   */
  individualst parents;

  /**
   * @brief
   *
   * @details
   */
  individualst children;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  bool can_mutate() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  bool can_cross() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  typename populationt::value_type &mutation_lhs();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const typename populationt::value_type &mutation_rhs() const;
};

#include "family_selection.inc"

#endif // CPROVER_CEGIS_GENETIC_FAMILY_SELECTION_H

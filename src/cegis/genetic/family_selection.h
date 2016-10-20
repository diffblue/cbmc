/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_FAMILY_SELECTION_H_
#define CEGIS_GENETIC_FAMILY_SELECTION_H_

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

#endif /* CEGIS_GENETIC_FAMILY_SELECTION_H_ */

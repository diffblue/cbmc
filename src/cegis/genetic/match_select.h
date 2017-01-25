/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_MATCH_SELECT_H
#define CPROVER_CEGIS_GENETIC_MATCH_SELECT_H

#include <functional>

#include <cegis/genetic/family_selection.h>

/**
 * @brief
 *
 * @details
 */
template<class population_typet>
class match_selectt
{
public:
  typedef population_typet populationt;
  typedef typename populationt::value_type individualt;
  typedef family_selectiont<populationt> selectiont;
  typedef typename selectiont::individualst individualst;
  typedef typename populationt::iterator contestantt;
  typedef std::map<const individualt *, std::list<bool> > test_case_datat;
private:
  const test_case_datat &test_case_data;
  const std::function<unsigned int()> next_random_unsigned_int;
  const size_t rounds;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param test_case_data
   * @param random
   * @param rounds
   */
  match_selectt(
      const test_case_datat &test_case_data,
      std::function<unsigned int()> random,
      size_t rounds);

  /**
   * @brief
   *
   * @details
   *
   * @param test_case_data
   * @param rounds
   */
  match_selectt(
      const test_case_datat &test_case_data,
      size_t rounds);

  /**
   * @brief
   *
   * @details
   */
  ~match_selectt();

  /**
   * @brief
   *
   * @details
   *
   * @param population
   *
   * @return
   */
  selectiont select(populationt &population) const;
};

#include "match_select.inc"

#endif // CPROVER_CEGIS_GENETIC_MATCH_SELECT_H

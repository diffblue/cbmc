/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_TOURNAMENT_SELECT_H_
#define CEGIS_GENETIC_TOURNAMENT_SELECT_H_

#include <cegis/value/program_individual.h>

/**
 * @brief
 *
 * @details
 */
template<class population_typet>
class tournament_selectt
{
  const size_t rounds;
public:
  typedef population_typet populationt;
  typedef typename populationt::value_type individualt;
  typedef family_selectiont<populationt> selectiont;
  typedef typename selectiont::individualst individualst;
  typedef typename populationt::iterator contestantt;

  /**
   * @brief
   *
   * @details
   *
   * @param random
   * @param rounds
   */
  tournament_selectt(size_t rounds);

  /**
   * @brief
   *
   * @details
   */
  ~tournament_selectt();

  /**
   * @brief
   *
   * @details
   *
   * @param population
   *
   * @return
   */
  selectiont select(populationt &population);
};

#include "tournament_select.inc"

#endif /* CEGIS_GENETIC_TOURNAMENT_SELECT_H_ */

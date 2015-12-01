/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_TOURNAMENT_SELECT_H_
#define CEGIS_GENETIC_TOURNAMENT_SELECT_H_

#include <cegis/value/program_individual.h>

/**
 * @brief
 *
 * @details
 */
class tournament_selectt
{
  class random_individualt &random;
  const size_t pop_size;
  const size_t rounds;
public:
  typedef program_populationt populationt;
  typedef populationt::value_type individualt;
  typedef std::deque<populationt::iterator> individualst;
  class selectiont
  {
  public:
    individualst parents;
    individualst children;

    bool can_mutate() const;
    bool can_cross() const;
    populationt::value_type &mutation_lhs();
    const populationt::value_type &mutation_rhs() const;
  };

  /**
   * @brief
   *
   * @details
   *
   * @param random
   * @param pop_size
   * @param rounds
   */
  tournament_selectt(random_individualt &random, size_t pop_size,
      size_t rounds);

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
   */
  void init(populationt &population);

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

#endif /* CEGIS_GENETIC_TOURNAMENT_SELECT_H_ */

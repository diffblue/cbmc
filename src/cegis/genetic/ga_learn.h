/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_GA_LEARN_H_
#define CEGIS_GENETIC_GA_LEARN_H_

#include <functional>

#include <cegis/danger/value/danger_goto_solution.h>

/**
 * @brief
 *
 * @details
 */
template<class selectt, class mutatet, class crosst, class fitnesst, class convertt>
class ga_learnt
{
public:
  typedef typename convertt::candidatet candidatet;
  typedef typename fitnesst::counterexamplet counterexamplet;
  typedef typename fitnesst::counterexamplest counterexamplest;
  typedef typename selectt::populationt populationt;
  typedef typename selectt::selectiont selectiont;
private:
  const class optionst &options;
  selectt &select;
  mutatet &mutate;
  crosst &cross;
  fitnesst &fitness;
  convertt &convert;
  populationt pop;
  selectiont selection;
  candidatet current_candidate;
  bool is_population_initialised;
  std::function<bool(void)> is_evolving;

  bool set_fitness(typename selectt::individualt &ind);
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param select
   * @param mutate
   * @param cross
   * @param fitness
   * @param convert
   */
  ga_learnt(const optionst &options, selectt &select, mutatet &mutate,
      crosst &cross, fitnesst &fitness, convertt &convert);

  /**
   * @brief
   *
   * @details
   */
  ~ga_learnt();


  /**
   * @brief
   *
   * @details
   *
   * @param seed
   */
  template<class seedt>
  void seed(seedt &seed);

  /**
   * @brief Provides the next candidate.
   *
   * @details Provides the last candidate generated using learn.
   *
   * @return The next candidate.
   */
  const candidatet &next_candidate() const;

  /**
   * @brief Generates a candidate solution.
   *
   * @details Receives set of counterexample from the verification oracle
   * and adds it to its information base. Generates a new candidate
   * based on received counterexamples.
   *
   * @param first The first iterator of the counterexample set.
   * @param last The last iterator of the counterexample set.
   *
   * @return <code>true</code> if learning was successful, <code>false</code>
   * if no new candidate could be generated.
   */
  template<class itert>
  bool learn(itert first, const itert &last);

  /**
   * @brief Displays the last candidate.
   *
   * @details Prints the last candidate generated using learn.
   *
   * @param os The stream to output the candidate.
   */
  void show_candidate(messaget::mstreamt &os) const;

  void show_candidate(messaget::mstreamt &os, const candidatet &candidate) const;

  /**
   * @brief
   *
   * @details
   *
   * @param min
   * @param max
   */
  void set_solution_size_range(size_t min, size_t max);

  /**
   * @brief
   *
   * @details
   *
   * @param is_evolving
   */
  void set_termination_condition(std::function<bool(void)> is_evolving);

  /**
   * @brief
   *
   * @details
   *
   * @param ind
   */
  void add_paragon(typename selectt::individualt ind);
};

#include "ga_learn.inc"

#endif /* CEGIS_GENETIC_GA_LEARN_H_ */

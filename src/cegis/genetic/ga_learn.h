/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_GA_LEARN_H
#define CPROVER_CEGIS_GENETIC_GA_LEARN_H

#include <chrono>
#include <functional>

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
  typedef typename selectt::individualt individualt;
  typedef individualt paragont;
  typedef typename selectt::selectiont selectiont;
private:
  typedef std::chrono::high_resolution_clock clockt;
  typedef clockt::time_point time_pointt;
  const class optionst &options;
  const std::function<void(individualt &)> havoc;
  selectt &select;
  mutatet &mutate;
  crosst &cross;
  fitnesst &fitness;
  convertt &convert;
  time_pointt program_startup;
  const size_t max_runtime_in_seconds;
  populationt pop;
  selectiont selection;
  candidatet current_candidate;
  std::function<bool(void)> is_evolving;

  bool set_fitness(individualt &ind);
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param random
   * @param select
   * @param mutate
   * @param cross
   * @param fitness
   * @param convert
   *
   * @tparam randomt
   */
  template<class randomt>
  ga_learnt(const optionst &options, randomt &random, selectt &select,
      mutatet &mutate, crosst &cross, fitnesst &fitness, convertt &convert);


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

  /**
   * @brief
   *
   * @details
   *
   * @param os
   * @param candidate
   */
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
  void add_paragon(paragont ind);
};

#include "ga_learn.inc"

#endif // CPROVER_CEGIS_GENETIC_GA_LEARN_H

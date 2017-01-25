/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SYMEX_CEGIS_SYMEX_LEARN_H
#define CPROVER_CEGIS_SYMEX_CEGIS_SYMEX_LEARN_H

#include <functional>

#include <goto-programs/safety_checker.h>

/**
 * @brief
 *
 * @details
 */
template<class preproct, class learn_configurationt>
class cegis_symex_learnt
{
public:
  typedef typename learn_configurationt::candidatet candidatet;
  typedef typename learn_configurationt::counterexamplet counterexamplet;
  typedef typename learn_configurationt::counterexamplest counterexamplest;
private:
  const class optionst &options;
  preproct &preproc;
  learn_configurationt &config;
  size_t word_width;
  size_t current_solution_size;
  size_t max_solution_size;
  candidatet current_candidate;
  const std::function<void(candidatet &)> default_candidate;
  counterexamplest counterexamples;

  safety_checkert::resultt run_bmc();
  bool learn_at_current_size();
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param preproc
   * @param config
   */
  cegis_symex_learnt(
      const optionst &options,
      preproct &preproc,
      learn_configurationt &config);

  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param preproc
   * @param config
   * @param default_candidate
   */
  cegis_symex_learnt(
      const optionst &options,
      preproct &preproc,
      learn_configurationt &config,
      const std::function<void(candidatet &)> &default_candidate);

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
  const candidatet &next_candidate();

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
   * @brief Adds explicit counterexamples.
   *
   * @details Adds counterexamples to the learner without starting a new learn round.
   *
   * @param first The first iterator of the counterexample set.
   * @param last The last iterator of the counterexample set.
   */
  template<class itert>
  void add_counterexamples(itert first, const itert &last);

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
   * @param min
   * @param max
   */
  void set_solution_size_range(size_t min, size_t max);
};

#include "cegis_symex_learn.inc"

#endif // CPROVER_CEGIS_SYMEX_CEGIS_SYMEX_LEARN_H

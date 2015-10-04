/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_CEGIS_SYMEX_LEARN_H_
#define CEGIS_DANGER_CEGIS_SYMEX_LEARN_H_

/**
 * @brief
 *
 * @details
 */
template<class learn_configurationt>
class cegis_symex_learnt
{
public:
  typedef typename learn_configurationt::candidatet candidatet;
  typedef typename learn_configurationt::counterexamplet counterexamplet;
  typedef typename learn_configurationt::counterexamplest counterexamplest;
private:
  const class optionst &options;
  learn_configurationt &config;
  size_t max_solution_size;
  candidatet current_candidate;
  counterexamplest counterexamples;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param config
   */
  cegis_symex_learnt(const optionst &options, learn_configurationt &config);

  /**
   * @brief
   *
   * @details
   */
  ~cegis_symex_learnt();

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
   * @details Generates a new candidate based on previously received counterexamples.
   * This operation is useful when the set of counterexamples remains the same and only
   * the maximum solution size has changed.
   *
   * @param max_solution_size The new maximum solution size.
   *
   * @return <code>true</code> if learning was successful, <code>false</code>
   * if no new candidate could be generated.
   */
  bool learn(size_t max_solution_size);

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
};

#include "cegis_symex_learn.inc"

#endif /* CEGIS_DANGER_CEGIS_SYMEX_LEARN_H_ */

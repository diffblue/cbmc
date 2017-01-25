/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_VERIFY_PARALLEL_DANGER_VERIFIER_H
#define CPROVER_CEGIS_DANGER_SYMEX_VERIFY_PARALLEL_DANGER_VERIFIER_H

#include <cegis/danger/symex/verify/danger_verify_config.h>

// TODO: Refactor this to use task_poolt.
/**
 * @brief
 *
 * @details
 */
class parallel_danger_verifiert
{
public:
  typedef danger_verify_configt::counterexamplet counterexamplet;
  typedef std::set<counterexamplet> counterexamplest;
private:
  const class optionst &options;
  danger_verify_configt &config;
  counterexamplest all_ces;
  bool is_failure;
public:
  typedef danger_verify_configt::candidatet candidatet;
  typedef counterexamplest::const_iterator const_iterator;

  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param config
   */
  parallel_danger_verifiert(const optionst &options, danger_verify_configt &config);

  /**
   * @brief
   *
   * @details
   */
  ~parallel_danger_verifiert();

  /**
   * @brief Verifies a given candidate solution.
   *
   * @details Effectively invokes CBMC using the given function bodies.
   *
   * @param candidate The candidate implementation provided by the learner.
   */
  void verify(const candidatet &candidate);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const_iterator counterexamples_begin() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const_iterator counterexamples_end() const;

  /**
   * @brief Indicates whether a counterexample could be produced.
   *
   * @details If the verification fails, but the oracle is unable to provide a
   * counterexample, this marks an error in the CBMC execution.
   *
   * @return <code>true</code> if a counterexample was created, <code>false</code> otherwise.
   */
  bool has_counterexamples() const;

  /**
   * @brief Indicates whether the provided solution holds.
   *
   * @details Provides the result of the last "verify()" operation.
   *
   * @return <code>true</code> if the last solution holds, <code>false</code> otherwise.
   */
  bool success() const;

  /**
   * @brief
   *
   * @details
   *
   * @param counterexample
   */
  void show_counterexample(
      messaget::mstreamt &os,
      const counterexamplet &counterexample) const;
};

#endif // CPROVER_CEGIS_DANGER_SYMEX_VERIFY_PARALLEL_DANGER_VERIFIER_H

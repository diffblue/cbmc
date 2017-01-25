/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SYMEX_CEGIS_SYMEX_VERIFY_H
#define CPROVER_CEGIS_SYMEX_CEGIS_SYMEX_VERIFY_H

#include <deque>
#include <util/message.h>

/**
 * @brief
 *
 * @details
 */
template<class verify_configurationt>
class cegis_symex_verifyt
{
public:
  typedef typename verify_configurationt::candidatet candidatet;
  typedef typename verify_configurationt::counterexamplet counterexamplet;
  typedef typename verify_configurationt::counterexamplest counterexamplest;
  typedef typename counterexamplest::const_iterator const_iterator;
private:
  const class optionst &options;
  verify_configurationt &config;
  counterexamplest current_counterexamples;
  bool is_failure;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param config
   */
  cegis_symex_verifyt(const optionst &options, verify_configurationt &config);

  /**
   * @brief Default destructor.
   *
   * @details No cleanup tasks performed.
   */
  ~cegis_symex_verifyt();

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

#include "cegis_symex_verify.inc"

#endif // CPROVER_CEGIS_SYMEX_CEGIS_SYMEX_VERIFY_H

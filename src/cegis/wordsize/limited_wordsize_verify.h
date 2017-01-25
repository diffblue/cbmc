/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_WORDSIZE_LIMITED_WORDSIZE_VERIFY_H
#define CPROVER_CEGIS_WORDSIZE_LIMITED_WORDSIZE_VERIFY_H

#include <deque>
#include <functional>

#include <util/message.h>

/**
 * @brief
 *
 * @details
 */
template<class verifyt>
class limited_wordsize_verifyt
{
  class optionst &options;
  verifyt &verifier;
  const std::function<void(size_t)> set_wordsize;
  bool is_success;
  size_t word_width;
public:
  typedef typename verifyt::candidatet candidatet;
  typedef typename verifyt::counterexamplet counterexamplet;
  typedef typename std::deque<counterexamplet> counterexamplest;
  typedef typename counterexamplest::const_iterator const_iterator;
private:
  counterexamplest ces;
  void verify_full(counterexamplest &ces, const candidatet &candidate);
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param verifier
   * @param set_wordsize
   */
  limited_wordsize_verifyt(optionst &options, verifyt &verifier,
      std::function<void(size_t)> set_wordsize);

  /**
   * @brief Default destructor.
   *
   * @details No cleanup tasks performed.
   */
  ~limited_wordsize_verifyt();

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
   * @param os
   * @param counterexample
   */
  void show_counterexample(
      messaget::mstreamt &os,
      const counterexamplet &counterexample) const;
};

#include "limited_wordsize_verify.inc"

#endif // CPROVER_CEGIS_WORDSIZE_LIMITED_WORDSIZE_VERIFY_H

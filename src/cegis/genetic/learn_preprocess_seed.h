/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_LEARN_PREPROCESS_SEED_H
#define CPROVER_CEGIS_GENETIC_LEARN_PREPROCESS_SEED_H

/**
 * @brief
 *
 * @details
 */
template<class learnt>
class learn_preprocess_seedt
{
  const class optionst &options;
  learnt &learn;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param learn
   */
  learn_preprocess_seedt(const optionst &options, learnt &learn);

  /**
   * @brief
   *
   * @details
   *
   * @param ces
   * @tparam ces
   */
  template<class cest>
  void operator()(cest &ces) const;
};

#include "learn_preprocess_seed.inc"

#endif // CPROVER_CEGIS_GENETIC_LEARN_PREPROCESS_SEED_H

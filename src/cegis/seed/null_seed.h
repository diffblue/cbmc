/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_NULL_SEED_H_
#define CEGIS_NULL_SEED_H_

#include <cegis/danger/symex/verify/danger_verify_config.h>

/**
 * @brief
 *
 * @details
 */
class null_seedt
{
public:
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

#include "null_seed.inc"

#endif /* CEGIS_NULL_SEED_H_ */

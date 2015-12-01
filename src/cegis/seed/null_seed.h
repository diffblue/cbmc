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
   */
  null_seedt();

  /**
   * @brief
   *
   * @details
   */
  ~null_seedt();

  /**
   * @brief
   *
   * @details
   *
   * @param ces
   */
  void operator()(danger_verify_configt::counterexamplest &ces) const;
};

#endif /* CEGIS_NULL_SEED_H_ */

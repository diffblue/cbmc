/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_LITERALS_SEED_H_
#define CEGIS_LITERALS_SEED_H_

#include <cegis/danger/symex/verify/danger_verify_config.h>

/**
 * @brief
 *
 * @details
 */
class danger_literals_seedt
{
  const danger_programt &prog;
  bool seeded;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog
   */
  danger_literals_seedt(const danger_programt &prog);

  /**
   * @brief
   *
   * @details
   */
  ~danger_literals_seedt();

  /**
   * @brief
   *
   * @details
   *
   * @param ces
   */
  void operator()(danger_verify_configt::counterexamplest &ces);
};

#endif /* CEGIS_LITERALS_SEED_H_ */

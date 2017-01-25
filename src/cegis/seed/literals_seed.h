/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SEED_LITERALS_SEED_H
#define CPROVER_CEGIS_SEED_LITERALS_SEED_H

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
  explicit danger_literals_seedt(const danger_programt &prog);

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

#endif // CPROVER_CEGIS_SEED_LITERALS_SEED_H

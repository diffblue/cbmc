/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_BODY_PROVIDER_H_
#define CEGIS_DANGER_BODY_PROVIDER_H_

#include <cegis/danger/options/danger_program.h>

/**
 * @brief
 *
 * @details
 */
class danger_body_providert
{
  const danger_programt &original_prog;
  danger_programt prog;
  bool initialised;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog
   */
  danger_body_providert(const danger_programt &prog);

  /**
   * @brief
   *
   * @details
   */
  ~danger_body_providert();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class goto_programt &operator()();
};

#endif /* CEGIS_DANGER_BODY_PROVIDER_H_ */

/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_OPTIONS_TARGET_COPY_HELPER_H
#define CPROVER_CEGIS_INVARIANT_OPTIONS_TARGET_COPY_HELPER_H

#include <cegis/invariant/options/invariant_program.h>

/**
 * @brief
 *
 * @details
 */
class target_copy_helpert
{
  const goto_programt::instructionst &old_instrs;
  goto_programt::instructionst &new_instrs;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param old_body
   * @param new_body
   */
  target_copy_helpert(const goto_programt &old_body, goto_programt &new_body);

  /**
   * @brief
   *
   * @details
   *
   * @param target
   *
   * @return
   */
  goto_programt::targett operator()(const goto_programt::targett &target) const;

  /**
   * @brief
   *
   * @details
   *
   * @param target_targets
   * @param src_targets
   *
   * @return
   */
  void operator()(
      goto_programt::targetst &target_targets,
      const goto_programt::targetst &src_targets) const;

  /**
   * @brief
   *
   * @details
   *
   * @param range
   *
   * @return
   */
  invariant_programt::program_ranget operator()(
      const invariant_programt::program_ranget &range) const;

  /**
   * @brief
   *
   * @details
   *
   * @param vars
   *
   * @return
   */
  invariant_programt::meta_vars_positionst operator()(
      const invariant_programt::meta_vars_positionst &vars) const;

  /**
   * @brief
   *
   * @details
   *
   * @param result
   * @param loop
   */
  void operator()(invariant_programt::invariant_loopt &result,
      const invariant_programt::invariant_loopt &loop) const;
};

#endif // CPROVER_CEGIS_INVARIANT_OPTIONS_TARGET_COPY_HELPER_H

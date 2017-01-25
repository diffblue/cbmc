/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_UTIL_COPY_INSTRUCTIONS_H
#define CPROVER_CEGIS_INVARIANT_UTIL_COPY_INSTRUCTIONS_H

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 */
class copy_instructionst
{
  typedef std::map<goto_programt::const_targett, goto_programt::targett> target_mapt;
  target_mapt target_mapping;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param new_target
   * @param old_target
   */
  void operator()(const goto_programt::targett &new_target,
      const goto_programt::const_targett &old_target);

  /**
   * @brief
   *
   * @details
   *
   * @param new_instrs
   * @param old_instrs
   */
  void operator()(
      goto_programt::instructionst &new_instrs,
      const goto_programt::instructionst &old_instrs);

  /**
   * @brief
   *
   * @details
   *
   * @param new_instrs
   * @param pos
   * @param old_instrs
   */
  goto_programt::targett operator()(
      goto_programt::instructionst &new_instrs,
      goto_programt::targett pos,
      const goto_programt::instructionst &old_instrs);

  /**
   * @brief
   *
   * @details
   */
  void finalize();

  /**
   * @brief
   *
   * @details
   *
   * @param new_target
   * @param old_target
   */
  void finalize(const goto_programt::targett &new_target,
      const goto_programt::const_targett &old_target);
};

/**
 * @brief
 *
 * @details
 *
 * @param instrs
 */
void invariant_make_presentable(goto_programt::instructionst &instrs);

/**
 * @brief
 *
 * @details
 *
 * @param target
 * @param source
 */
void copy_instructions(
    goto_programt::instructionst &target,
    const goto_programt::instructionst &source);

/**
 * @brief
 *
 * @details
 *
 * @param target
 * @param pos
 * @param source
 */
goto_programt::targett copy_instructions(
    goto_programt::instructionst &target,
    goto_programt::targett pos,
    const goto_programt::instructionst &source);

#endif // CPROVER_CEGIS_INVARIANT_UTIL_COPY_INSTRUCTIONS_H

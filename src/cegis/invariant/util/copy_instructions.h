/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_COPY_INSTRUCTIONS_H_
#define CEGIS_DANGER_COPY_INSTRUCTIONS_H_

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
   * @param old_offset
   */
  copy_instructionst();

  /**
   * @brief
   *
   * @details
   */
  ~copy_instructionst();

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

#endif /* SRC_CEGIS_DANGER_UTIL_COPY_INSTRUCTIONS_H_ */

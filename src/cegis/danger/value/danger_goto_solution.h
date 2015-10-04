/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_GOTO_SOLUTION_H_
#define CEGIS_DANGER_GOTO_SOLUTION_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 */
class danger_goto_solutiont
{
public:
  /**
   * @brief
   *
   * @details
   */
  struct danger_programt
  {
    goto_programt::instructionst invariant;
    goto_programt::instructionst ranking;
    goto_programt::instructionst skolem;
  };
  typedef std::vector<danger_programt> danger_programst;
  danger_programst danger_programs;

  typedef std::vector<exprt> nondet_choicest;
  nondet_choicest x0_choices;
};

#endif /* CEGIS_DANGER_GOTO_SOLUTION_H_ */

/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_VALUE_JSA_SOLUTION_H
#define CPROVER_CEGIS_JSA_VALUE_JSA_SOLUTION_H

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 */
class jsa_solutiont
{
public:
  typedef std::vector<goto_programt::instructionst> predicatest;

  /**
   * @brief
   *
   * @details
   */
  predicatest predicates;

  /**
   * @brief
   *
   * @details
   */
  goto_programt::instructionst query;

  /**
   * @brief
   *
   * @details
   */
  goto_programt::instructionst invariant;

  /**
   * @brief
   *
   * @details
   */
  size_t max_size;

  /**
   * @brief
   *
   * @details
   */
  jsa_solutiont();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  jsa_solutiont(const jsa_solutiont &other);

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  jsa_solutiont &operator=(const jsa_solutiont &other);

  /**
   * @brief
   *
   * @details
   */
  void clear();
};

#endif // CPROVER_CEGIS_JSA_VALUE_JSA_SOLUTION_H

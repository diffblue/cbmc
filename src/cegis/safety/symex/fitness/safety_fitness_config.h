/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_SYMEX_FITNESS_SAFETY_FITNESS_CONFIG_H
#define CPROVER_CEGIS_SAFETY_SYMEX_FITNESS_SAFETY_FITNESS_CONFIG_H

#include <util/message.h>

#include <cegis/safety/options/safety_program.h>
#include <cegis/safety/value/safety_goto_solution.h>

/**
 * @brief
 *
 * @details
 */
class safety_fitness_configt
{
  class instruction_set_info_factoryt &info_fac;
  const safety_programt &original_program;
  safety_programt program_with_constraint;
  goto_programt::targetst original_quantifiers;
  safety_programt program;
  goto_programt::targetst quantifiers;
  bool constraint_inserted;
  bool program_contains_ce;
  size_t max_solution_size;
public:
  typedef safety_goto_solutiont candidatet;
  typedef class safety_goto_cet counterexamplet;
  typedef class program_individualt individualt;

  /**
   * @brief
   *
   * @details
   *
   * @param info_fac
   * @param prog
   */
  safety_fitness_configt(instruction_set_info_factoryt &info_fac,
      const safety_programt &prog);

  /**
   * @brief
   *
   * @details
   */
  ~safety_fitness_configt();

  /**
   * @brief
   *
   * @details
   *
   * @param candidate
   */
  void set_candidate(const candidatet &candidate);

  /**
   * @brief
   *
   * @details
   *
   * @param ce
   */
  void set_test_case(const counterexamplet &ce);

  /**
   * @brief
   *
   * @details
   *
   * @param current_candidate
   * @param ind
   */
  void convert(candidatet &current_candidate, const individualt &ind);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class symbol_tablet &get_symbol_table() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class goto_functionst &get_goto_functions() const;

  /**
   * @brief
   *
   * @details
   *
   * @param size
   */
  void set_max_solution_size(size_t size);

  /**
   * @brief
   *
   * @details
   *
   * @param candidate
   * @param os
   */
  void show(messaget::mstreamt &os, const candidatet &candidate) const;
};

#endif // CPROVER_CEGIS_SAFETY_SYMEX_FITNESS_SAFETY_FITNESS_CONFIG_H

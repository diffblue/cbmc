/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_FITNESS_DANGER_FITNESS_CONFIG_H
#define CPROVER_CEGIS_DANGER_SYMEX_FITNESS_DANGER_FITNESS_CONFIG_H

#include <cegis/danger/options/danger_program.h>

/**
 * @brief
 *
 * @details
 */
class danger_fitness_configt
{
  class instruction_set_info_factoryt &info_fac;
  const danger_programt &original_program;
  danger_programt program_with_constraint;
  goto_programt::targetst original_quantifiers;
  danger_programt program;
  goto_programt::targetst quantifiers;
  bool constraint_inserted;
  bool program_contains_ce;
  size_t max_solution_size;
public:
  typedef class danger_goto_solutiont candidatet;
  typedef std::map<const irep_idt, exprt> counterexamplet;
  typedef class program_individualt individualt;

  /**
   * @brief
   *
   * @details
   *
   * @param info_fac
   * @param prog
   */
  danger_fitness_configt(instruction_set_info_factoryt &info_fac,
      const danger_programt &prog);

  /**
   * @brief
   *
   * @details
   */
  ~danger_fitness_configt();

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

#endif // CPROVER_CEGIS_DANGER_SYMEX_FITNESS_DANGER_FITNESS_CONFIG_H

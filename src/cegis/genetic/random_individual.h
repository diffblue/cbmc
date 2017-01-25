/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_RANDOM_INDIVIDUAL_H
#define CPROVER_CEGIS_GENETIC_RANDOM_INDIVIDUAL_H

#include <util/type.h>

#include <cegis/value/program_individual.h>
#include <cegis/genetic/instruction_set_info_factory.h>

/**
 * @brief
 *
 * @details
 */
class random_individualt
{
  const typet type;
  instruction_set_info_factoryt info_factory;
  class genetic_settingst &settings;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param type
   * @param instruction_set_info_factory
   * @param settings
   */
  random_individualt(const typet &type,
      const instruction_set_info_factoryt &info_factory,
      genetic_settingst &settings);

  /**
   * @brief
   *
   * @details
   */
  ~random_individualt();

  /**
   * @brief
   *
   * @details
   *
   * @param index
   *
   * @return
   */
  program_individualt::programt::size_type prog_size(size_t index) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  program_individualt::instructiont::opcodet opcode();

  /**
   * @brief
   *
   * @details
   *
   * @param instr_index
   *
   * @return
   */
  program_individualt::instructiont::opt op(size_t instr_index) const;

  /**
   * @brief
   *
   * @details
   *
   * @param instr
   * @param index
   */
  void havoc(program_individualt::instructiont &instr, size_t index);

  /**
   * @brief
   *
   * @details
   *
   * @param prog
   * @param index
   */
  void havoc(program_individualt::programt &prog, size_t index);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  program_individualt::x0t::value_type x0() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  program_individualt::x0t::value_type constant() const;

  /**
   * @brief
   *
   * @details
   *
   * @param ind
   */
  void havoc(program_individualt &ind);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  unsigned int rand() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  size_t get_num_vars() const;

  /**
   * @brief
   *
   * @details
   *
   * @param prog_index
   *
   * @return
   */
  size_t get_max_prog_size(size_t prog_index) const;

  /**
   * @brief
   *
   * @details
   *
   * @param prog_index
   *
   * @return
   */
  size_t get_min_prog_size(size_t prog_index) const;

  /**
   * @brief
   *
   * @details
   *
   * @param ind
   */
  void post_process(program_individualt &ind) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  operator std::function<unsigned int()>() const;
};

#endif // CPROVER_CEGIS_GENETIC_RANDOM_INDIVIDUAL_H

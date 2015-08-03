/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_SYMEX_TARGET_PROGRAM_FACTORY_H_
#define CEGIS_SYMEX_TARGET_PROGRAM_FACTORY_H_

/**
 * @brief
 *
 * @details
 *
 * @param symbol_table
 * @param goto_functions
 * @param options
 */
void add_target_programs(class symbol_tablet &symbol_table,
    class goto_functionst &goto_functions, const class cegis_optionst &options,
    class source_location_factoryt &lfactory);

/**
 * @brief
 *
 * @details
 */
class target_program_factoryt
{
  symbol_tablet &symbol_table;
  goto_functionst &gf;
  const cegis_optionst &options;
  source_location_factoryt &lfactory;
public:
  /**
   * @brief
   *
   * @details
   */
  target_program_factoryt(symbol_tablet &symbol_table,
      goto_functionst &goto_functions, const cegis_optionst &options,
      source_location_factoryt &lfactory);

  /**
   * @brief
   *
   * @details
   */
  ~target_program_factoryt();

  /**
   * @brief
   *
   * @details
   */
  void operator()() const;
};

#endif /* CEGIS_SYMEX_TARGET_PROGRAM_FACTORY_H_ */

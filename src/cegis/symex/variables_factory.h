/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_VARIABLES_FACTORY_H_
#define CEGIS_VARIABLES_FACTORY_H_

#include <util/std_expr.h>

/**
 * @brief
 *
 * @details
 *
 * @param symbol_table
 * @param synthesis_entry
 * @param synthesis_entry_function_name
 * @param source_location_factory
 * @param max_prog_size
 */
void create_symex_learning_variables(symbol_tablet &symbol_table,
    class goto_functionst &goto_functions, const class cegis_optionst &options,
    class source_location_factoryt &source_location_factory);

/**
 * @brief Helper class for synthesis variables access.
 *
 * @details Synthesis algorithms which use goto-programs as intermediate
 * representation need unified access to existing variables as well
 * as temporary variables. This class provides services to simplify this
 * task.
 */
class variables_factoryt
{
  symbol_tablet &symbol_table;
  goto_functionst &gf;
  const cegis_optionst &options;
  source_location_factoryt &loc_fac;
public:
  /**
   * @brief Creates a synthesis variables factory.
   *
   * @details Creates a variables factory which introduces variables
   * necessary for synthesis into the given symbol table. Temporary
   * variables are limited by the given maximum program size.
   *
   * @param symbol_table The symbol table to introduce the synthesis
   * variables into.
   * @param goto_functions
   * @param options
   * @param source_location_factory Factory providing source locations for
   * newly introduced
   */
  variables_factoryt(symbol_tablet &symbol_table,
      goto_functionst &goto_functions, const cegis_optionst &options,
      source_location_factoryt &source_location_factory);

  /**
   * @brief Default destructor.
   *
   * @details No cleanup tasks performed.
   */
  ~variables_factoryt();

  /**
   * @brief Single main operation.
   *
   * @details Effectively executes the implemented operation.
   */
  void operator()() const;
};

#endif /* CEGIS_VARIABLES_FACTORY_H_ */

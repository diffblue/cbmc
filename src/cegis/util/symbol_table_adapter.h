/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_UTIL_SYMBOL_TABLE_ADAPTER_H_
#define CEGIS_UTIL_SYMBOL_TABLE_ADAPTER_H_

#include <util/irep.h>

/**
 * @brief
 *
 * @details
 */
class symbol_table_adaptert
{
  class symbol_tablet &st;
public:
  /**
   * @brief
   *
   * @details
   */
  symbol_table_adaptert(symbol_tablet &st);

  /**
   * @brief
   *
   * @details
   */
  ~symbol_table_adaptert();

  /**
   * @brief
   *
   * @details
   *
   * @param name
   * @param type
   * @param loc
   */
  void add_global_constant(const irep_idt &name, const class typet &type,
      const class source_locationt &loc) const;

  /**
   * @brief
   *
   * @details
   *
   * @param name
   * @param value
   * @param gf
   * @param loc
   */
  void add_global_constant(const irep_idt &name, const class exprt &value,
      class goto_functionst &gf, const source_locationt &loc) const;
};

#endif /* CEGIS_UTIL_SYMBOL_TABLE_ADAPTER_H_ */

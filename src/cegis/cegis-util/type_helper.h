/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_UTIL_TYPE_HELPER_H_
#define CEGIS_UTIL_TYPE_HELPER_H_

#include <set>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param type
 */
const class typet &replace_struct_by_symbol_type(
    const class symbol_tablet &st,
    const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param lhs
 * @param rhs
 * @param st
 */
bool instanceof(const symbol_tablet &st, const typet &lhs, const typet &rhs);

/**
 * @brief
 *
 * @details
 */
class instanceof_anyt
{
  const symbol_tablet &st;
  const std::set<typet> &types;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param types
   */
  instanceof_anyt(const symbol_tablet &st, const std::set<typet> &types);

  /**
   * @brief
   *
   * @details
   *
   * @param type
   *
   * @return
   */
  bool operator()(const typet &type) const;
};

#endif /* CEGIS_UTIL_TYPE_HELPER_H_ */

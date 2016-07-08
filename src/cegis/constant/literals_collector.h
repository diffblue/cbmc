/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_LITERALS_COLLECTOR_H_
#define CEGIS_LITERALS_COLLECTOR_H_

#include <util/std_expr.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 *
 * @return
 */
std::vector<constant_exprt> collect_integer_literals(
    const class symbol_tablet &st,
    const class goto_functionst &gf);

#endif /* CEGIS_LITERALS_COLLECTOR_H_ */

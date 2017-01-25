/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONSTANT_LITERALS_COLLECTOR_H
#define CPROVER_CEGIS_CONSTANT_LITERALS_COLLECTOR_H

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

#endif // CPROVER_CEGIS_CONSTANT_LITERALS_COLLECTOR_H

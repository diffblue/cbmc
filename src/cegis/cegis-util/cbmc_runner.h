/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_UTIL_CBMC_RUNNER_H_
#define CEGIS_UTIL_CBMC_RUNNER_H_

#include <goto-programs/safety_checker.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param result
 */
safety_checkert::resultt run_cbmc(
    const class symbol_tablet &st,
    const class goto_functionst &gf,
    class goto_tracet &result);

#endif /* CEGIS_UTIL_CBMC_RUNNER_H_ */

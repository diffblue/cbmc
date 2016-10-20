/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_UTIL_CBMC_RUNNER_H_
#define CEGIS_UTIL_CBMC_RUNNER_H_

#include <goto-programs/safety_checker.h>

/**
 * @brief CBMC run result class.
 *
 * @details Result class with all referenced entities in place
 * to avoid undefined behaviour when analysing trace results
 * which refer to the GOTO program.
 */
class cbmc_resultt
{
public:
  goto_functionst goto_functions;
  symbol_tablet symbol_table;
  goto_tracet trace;
};

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param result
 * @param keep_goto_programs
 *
 * @return
 */
safety_checkert::resultt run_cbmc(
    const class symbol_tablet &st,
    const class goto_functionst &gf,
    cbmc_resultt &result,
    bool keep_goto_programs);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param result
 * @param options
 *
 * @return
 */
safety_checkert::resultt run_cbmc(
    const class symbol_tablet &st,
    const class goto_functionst &gf,
    cbmc_resultt &result,
    const optionst &options);

#endif /* CEGIS_UTIL_CBMC_RUNNER_H_ */

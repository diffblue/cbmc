/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_RUNNER_H_
#define CEGIS_JSA_RUNNER_H_

#include <util/message.h>

/**
 * @brief
 *
 * @details
 *
 * @param options
 * @param result
 * @param st
 * @param gf
 *
 * @return
 */
int run_jsa(class optionst &options, messaget::mstreamt &result,
    const class symbol_tablet &st, const class goto_functionst &gf);

#endif /* CEGIS_JSA_RUNNER_H_ */

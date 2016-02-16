/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_RUNNER_H_
#define CEGIS_DANGER_RUNNER_H_

#include <util/message.h>

/**
 * @brief
 *
 * @details
 *
 * @param cmdline
 * @param options
 * @param result
 * @param st
 * @param gf
 *
 * @return
 */
int run_danger(class optionst &options, class messaget::mstreamt &result,
    const class symbol_tablet &st, const class goto_functionst &gf);

#endif /* CEGIS_DANGER_RUNNER_H_ */

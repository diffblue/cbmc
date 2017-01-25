/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_FACADE_RUNNER_HELPER_H
#define CPROVER_CEGIS_FACADE_RUNNER_HELPER_H

#include <util/message.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param opt
 * @paral learn
 * @param verify
 * @param preproc
 *
 * @tparam learnt
 * @tparam verifyt
 * @tparam preproct
 */
template<class learnt, class verifyt, class preproct>
int run_cegis_with_statistics_wrapper(
    messaget::mstreamt &os,
    const class optionst &opt,
    learnt &learn,
    verifyt &verify,
    preproct &preproc);

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param opt
 * @paral learn
 * @param verify
 * @param preproc
 * @param seed
 *
 * @tparam learnt
 * @tparam verifyt
 * @tparam preproct
 * @tparam seedt
 */
template<class learnt, class verifyt, class preproct, class seedt>
int run_cegis_with_statistics_wrapper(
    messaget::mstreamt &os,
    const class optionst &opt,
    learnt &learn,
    verifyt &verify,
    preproct &preproc,
    seedt &seed);

#include "runner_helper.inc"

#endif // CPROVER_CEGIS_FACADE_RUNNER_HELPER_H

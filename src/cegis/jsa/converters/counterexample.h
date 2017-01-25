/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_CONVERTERS_COUNTEREXAMPLE_H
#define CPROVER_CEGIS_JSA_CONVERTERS_COUNTEREXAMPLE_H

#include <cegis/jsa/value/jsa_genetic_synthesis.h>
#include <cegis/jsa/value/jsa_counterexample.h>

/**
 * @brief
 *
 * @details
 *
 * @param counterexample
 *
 * @return
 */
size_t count_heaps(const jsa_counterexamplet &counterexample);

/**
 * @brief
 *
 * @details
 *
 * @param counterexample
 * @param heaps
 *
 * @return
 */
void retrieve_heaps(
    const jsa_counterexamplet &counterexample,
    __CPROVER_jsa_abstract_heapt *heaps);

/**
 * @brief
 *
 * @details
 *
 * @param counterexample
 *
 * @return
 */
size_t count_words(const jsa_counterexamplet &counterexample);

/**
 * @brief
 *
 * @details
 *
 * @param counterexample
 * @param words
 *
 * @return
 */
void retrieve_words(
    const jsa_counterexamplet &counterexample,
    __CPROVER_jsa_word_t *words);

#endif // CPROVER_CEGIS_JSA_CONVERTERS_COUNTEREXAMPLE_H

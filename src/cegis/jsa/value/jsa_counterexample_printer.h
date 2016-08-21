/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_COUNTEREXAMPLE_PRINTER_H_
#define CEGIS_JSA_COUNTEREXAMPLE_PRINTER_H_

#include <util/message.h>

#include <cegis/jsa/value/jsa_counterexample.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param counterexample
 */
void print_jsa_counterexample(
    messaget::mstreamt &os,
    const jsa_counterexamplet &counterexample);

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param first
 * @param last
 */
template<class counterexamplet_itert>
void print_jsa_counterexample(
    messaget::mstreamt &os,
    counterexamplet_itert first,
    counterexamplet_itert last);

#include <cegis/jsa/value/jsa_counterexample_printer.inc>

#endif /* CEGIS_JSA_COUNTEREXAMPLE_PRINTER_H_ */

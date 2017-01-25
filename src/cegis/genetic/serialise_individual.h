/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_SERIALISE_INDIVIDUAL_H
#define CPROVER_CEGIS_GENETIC_SERIALISE_INDIVIDUAL_H

#include <deque>
#include <functional>

#include <util/expr.h>

/**
 * @brief
 *
 * @details
 *
 * @param stream
 * @param ind
 * @param max_prog_sz
 */
void serialise(std::deque<unsigned int> &stream,
    const class program_individualt &ind,
    const std::function<size_t(size_t)> max_prog_sz);

/**
 * @brief
 *
 * @details
 *
 * @param stream
 * @param assignments
 */
void serialise(std::deque<unsigned int> &stream,
    const std::map<const irep_idt, exprt> assignments);

#endif // CPROVER_CEGIS_GENETIC_SERIALISE_INDIVIDUAL_H

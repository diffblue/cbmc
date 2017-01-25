/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_VALUE_ASSIGNMENTS_PRINTER_H
#define CPROVER_CEGIS_VALUE_ASSIGNMENTS_PRINTER_H

#include <util/message.h>
#include <util/expr.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param st
 * @param assignments
 */
void print_assignments(
    messaget::mstreamt &os,
    const class symbol_tablet &st,
    const std::map<const irep_idt, exprt> &assignments);

#endif // CPROVER_CEGIS_VALUE_ASSIGNMENTS_PRINTER_H

/*******************************************************************\

Module: Add parameter assignments

Author: Daniel Kroening

Date:   September 2015

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_PARAMETER_ASSIGNMENTS_H
#define CPROVER_GOTO_PROGRAMS_PARAMETER_ASSIGNMENTS_H

#include <goto-programs/goto_model.h>

void parameter_assignments(symbol_tablet &, goto_functionst &);

void parameter_assignments(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_PARAMETER_ASSIGNMENTS_H

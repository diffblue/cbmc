/*******************************************************************\

Module: Add parameter assignments

Author: Daniel Kroening

Date:   September 2015

\*******************************************************************/

/// \file
/// Add parameter assignments

#ifndef CPROVER_GOTO_PROGRAMS_PARAMETER_ASSIGNMENTS_H
#define CPROVER_GOTO_PROGRAMS_PARAMETER_ASSIGNMENTS_H

class goto_functionst;
class goto_modelt;
class symbol_tablet;

void parameter_assignments(symbol_tablet &, goto_functionst &);

void parameter_assignments(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_PARAMETER_ASSIGNMENTS_H

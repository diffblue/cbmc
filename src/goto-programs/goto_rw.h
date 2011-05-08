/*******************************************************************\

Module: 

Author: Daniel Kroening

Date: April 2010

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_RW_H
#define CPROVER_GOTO_PROGRAMS_GOTO_RW_H

#include "goto_program.h"

void goto_rw(const goto_programt::instructiont &,
             std::list<exprt> &read, std::list<exprt> &write);

#endif

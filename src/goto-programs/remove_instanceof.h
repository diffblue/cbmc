/*******************************************************************\

Module: Remove Instance-of Operators

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_INSTANCEOF_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_INSTANCEOF_H

#include <util/symbol_table.h>
#include "goto_functions.h"

void remove_instanceof(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions);


#endif

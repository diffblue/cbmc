/*******************************************************************\

Module: Remove 'asm' statements by compiling into suitable standard
        code

Author: Daniel Kroening

Date:   December 2014

\*******************************************************************/

/// \file
/// Remove 'asm' statements by compiling into suitable standard code

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H

#include <goto-programs/goto_model.h>

void remove_asm(
  goto_functionst::goto_functiont &goto_function,
  symbol_tablet &symbol_table);

void remove_asm(goto_functionst &goto_functions, symbol_tablet &symbol_table);

void remove_asm(goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H

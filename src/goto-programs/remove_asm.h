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

#include <goto-programs/goto_functions.h>

class goto_modelt;
class symbol_tablet;

void remove_asm(goto_functionst &, symbol_tablet &);

void remove_asm(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H

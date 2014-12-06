/*******************************************************************\

Module: Remove 'asm' statements by compiling into suitable standard
        code

Author: Daniel Kroening

Date:   December 2014

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H

#include <goto-programs/goto_model.h>

void remove_asm(symbol_tablet &, goto_functionst &);

void remove_asm(goto_modelt &);

#endif

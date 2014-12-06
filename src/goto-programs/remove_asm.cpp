/*******************************************************************\

Module: Remove 'asm' statements by compiling into suitable standard
        code

Author: Daniel Kroening

Date:   December 2014

\*******************************************************************/

#include "remove_asm.h"

/*******************************************************************\

Function: remove_asm

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asm(
  goto_programt::instructiont &instruction,
  symbol_tablet &symbol_table)
{
}

/*******************************************************************\

Function: remove_asm

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asm(
  goto_functionst::goto_functiont &goto_function,
  symbol_tablet &symbol_table)
{
  Forall_goto_program_instructions(it, goto_function.body)
  {
    remove_asm(*it, symbol_table);
  }
}

/*******************************************************************\

Function: remove_asm

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asm(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    remove_asm(it->second, symbol_table);
}

/*******************************************************************\

Function: remove_asm

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asm(goto_modelt &goto_model)
{
  remove_asm(goto_model.symbol_table, goto_model.goto_functions);
}


/*******************************************************************\

Module: goto_programt -> irep conversion

Author: CM Wintersteiger

Date: May 2007

\*******************************************************************/

#ifndef GOTO_PROGRAM_IREP_H_
#define GOTO_PROGRAM_IREP_H_

#include <goto-programs/goto_program.h>

void convert(const goto_programt::instructiont &instruction, irept &irep);
void convert(const irept &irep, goto_programt::instructiont &instruction);

void convert(const goto_programt &program, irept &irep);
void convert(const irept &irep, goto_programt &program);

#endif /*GOTO_PROGRAM_IREP_H_*/

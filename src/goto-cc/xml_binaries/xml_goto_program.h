/*******************************************************************\
 
Module: Convert goto programs into xml structures and back
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef XML_GOTO_PROGRAM_H_
#define XML_GOTO_PROGRAM_H_

#include <goto-programs/goto_program.h>
#include <util/xml.h>

void convert(
  const goto_programt&,
  xmlt&);
  
void convert(
  const xmlt&,
  goto_programt&);
	
goto_programt::targett find_instruction(
  const xmlt &, 
  goto_programt::instructionst &, 
  const irep_idt &);

#endif /*XML_GOTO_PROGRAM_H_*/

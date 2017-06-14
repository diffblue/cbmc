/*******************************************************************\

Module: Convert goto programs into xml structures and back

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Convert goto programs into xml structures and back

#ifndef CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_PROGRAM_H
#define CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_PROGRAM_H

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

#endif // CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_PROGRAM_H

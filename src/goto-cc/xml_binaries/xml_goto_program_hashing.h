/*******************************************************************\

Module: Convert goto programs into xml structures and back (with
        irep hashing)

Author: CM Wintersteiger

Date: July 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_PROGRAM_HASHING_H
#define CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_PROGRAM_HASHING_H

#include <goto-programs/goto_program.h>
#include <util/xml.h>

#include "xml_irep_hashing.h"

class xml_goto_program_convertt {
  private:
    xml_irep_convertt irepconverter;
  public:
    explicit xml_goto_program_convertt(xml_irep_convertt::ireps_containert &ic) :
      irepconverter(ic) {};

  void convert(const goto_programt&, xmlt&);
  void convert(const xmlt&, goto_programt&);

  goto_programt::targett
  find_instruction( const xmlt &,
                    goto_programt::instructionst &,
                    const std::string &);
};




#endif // CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_PROGRAM_HASHING_H

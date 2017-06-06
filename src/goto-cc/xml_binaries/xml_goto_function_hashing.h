/*******************************************************************\

Module: Convert goto functions into xml structures and back (with irep
        hashing).

Author: CM Wintersteiger

Date: July 2006

\*******************************************************************/

/// \file
/// Convert goto functions into xml structures and back (with irep hashing).

#ifndef CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_FUNCTION_HASHING_H
#define CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_FUNCTION_HASHING_H

#include <util/xml.h>
#include <goto-programs/goto_functions.h>

#include "xml_irep_hashing.h"

class xml_goto_function_convertt
{
private:
  xml_irep_convertt::ireps_containert &ireps_container;

public:
  explicit xml_goto_function_convertt(xml_irep_convertt::ireps_containert &ic):
    ireps_container(ic)
  {
  }

  void convert(const xmlt&, goto_functionst::goto_functiont&);
  void convert(const goto_functionst::goto_functiont&, xmlt&);
};

#endif // CPROVER_GOTO_CC_XML_BINARIES_XML_GOTO_FUNCTION_HASHING_H

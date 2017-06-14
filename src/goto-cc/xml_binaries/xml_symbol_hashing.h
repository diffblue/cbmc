/*******************************************************************\

Module: XML-symbol conversions with irep hashing

Author: CM Wintersteiger

Date: July 2006

\*******************************************************************/

/// \file
/// XML-symbol conversions with irep hashing

#ifndef CPROVER_GOTO_CC_XML_BINARIES_XML_SYMBOL_HASHING_H
#define CPROVER_GOTO_CC_XML_BINARIES_XML_SYMBOL_HASHING_H

#include <util/symbol.h>
#include <util/xml.h>

#include "xml_irep_hashing.h"

class xml_symbol_convertt
{
private:
  xml_irep_convertt irepconverter;
  std::list<irept> irepcache;

public:
  explicit xml_symbol_convertt(xml_irep_convertt::ireps_containert &ic):
    irepconverter(ic)
  {
  }

  void convert(const symbolt &, xmlt &);
  void convert(const xmlt &, symbolt &);
};

#endif // CPROVER_GOTO_CC_XML_BINARIES_XML_SYMBOL_HASHING_H

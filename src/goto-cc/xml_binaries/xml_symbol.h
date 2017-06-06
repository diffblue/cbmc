/*******************************************************************\

Module: Converts symbols to xml structures and back.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Converts symbols to xml structures and back.

#ifndef CPROVER_GOTO_CC_XML_BINARIES_XML_SYMBOL_H
#define CPROVER_GOTO_CC_XML_BINARIES_XML_SYMBOL_H

#include <util/symbol.h>
#include <util/xml.h>

void convert(const symbolt &, xmlt &);
void convert(const xmlt &, symbolt &);

#endif // CPROVER_GOTO_CC_XML_BINARIES_XML_SYMBOL_H

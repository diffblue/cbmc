/*******************************************************************\

Module: XML-symbol conversions with irep hashing

Author: CM Wintersteiger

Date: July 2006

\*******************************************************************/

/// \file
/// XML-symbol conversions with irep hashing

#include "xml_irep_hashing.h"

#include "xml_symbol_hashing.h"

/// converts a symbol to an xml symbol node
/// \par parameters: a symbol and an xml node
/// \return none
void xml_symbol_convertt::convert(const symbolt &sym, xmlt &root)
{
  xmlt &xmlsym = root.new_element("symbol");
  irepcache.push_back(irept());
  sym.to_irep(irepcache.back());
  irepconverter.reference_convert(irepcache.back(), xmlsym);
}

/// converts an xml symbol node to a symbol
/// \par parameters: an xml node and a symbol
/// \return none
void xml_symbol_convertt::convert(const xmlt &xmlsym, symbolt &symbol)
{
  irept t;

  irepconverter.convert(xmlsym, t);
  irepconverter.resolve_references(t);
  symbol.from_irep(t);
}

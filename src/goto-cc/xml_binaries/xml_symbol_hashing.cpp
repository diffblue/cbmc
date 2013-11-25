/*******************************************************************\
 
Module: XML-symbol conversions with irep hashing
 
Author: CM Wintersteiger
 
Date: July 2006
 
\*******************************************************************/

#include "xml_symbol_hashing.h"
#include "xml_irep_hashing.h"

/*******************************************************************\
 
Function: xml_symbol_convertt::convert
 
  Inputs: a symbol and an xml node
 
 Outputs: none
 
 Purpose: converts a symbol to an xml symbol node
 
\*******************************************************************/

void xml_symbol_convertt::convert(const symbolt& sym, xmlt &root)
{
  xmlt &xmlsym = root.new_element("symbol");
  irepcache.push_back(irept());
  sym.to_irep(irepcache.back());  
  irepconverter.reference_convert(irepcache.back(), xmlsym);
}

/*******************************************************************\
 
Function: xml_symbol_convertt::convert
 
  Inputs: an xml node and a symbol
 
 Outputs: none
 
 Purpose: converts an xml symbol node to a symbol
 
\*******************************************************************/

void xml_symbol_convertt::convert(const xmlt &xmlsym, symbolt& symbol)
{  
  irept t;
  
  irepconverter.convert(xmlsym, t);
  irepconverter.resolve_references(t);
  symbol.from_irep(t); 
}

/*******************************************************************\
 
Module: Symbol to binary conversions with irep hashing
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#include "symbol_serialization.h"
#include "irep_serialization.h"
#include "symbol.h"

/*******************************************************************\
 
Function: symbol_serializationt::convert
 
  Inputs: a symbol and an xml node
 
 Outputs: none
 
 Purpose: converts a symbol to binary format and outputs it
 
\*******************************************************************/

void symbol_serializationt::convert(const symbolt& sym, std::ostream &out)
{
  irepcache.push_back(irept());
  sym.to_irep(irepcache.back());  
  irepconverter.reference_convert(irepcache.back(), out);
}

/*******************************************************************\
 
Function: symbol_serializationt::convert
 
  Inputs: an xml node and a symbol
 
 Outputs: none
 
 Purpose: inputs a symbol from a binary stream and converts it 
          into a symbolt
 
\*******************************************************************/

void symbol_serializationt::convert(std::istream& in, irept& symrep)
{  
  irepconverter.reference_convert(in, symrep);
  // reference is not resolved here! 
}

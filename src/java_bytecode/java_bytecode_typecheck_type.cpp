/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>

#include "java_bytecode_typecheck.h"

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_type(typet &type)
{ 
  if(type.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_type(type).get_identifier();
    
    // does it exist already in the symbol table?
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);
    
    if(s_it==symbol_table.symbols.end())
    {
      // parse the symbol; the type is in the suffix
      std::size_t colon_pos=id2string(identifier).rfind(':');
      if(colon_pos==std::string::npos)
        throw "mal-formed Java identifier: `"+id2string(identifier)+"'";

      // no, create the symbol
      symbolt new_symbol;
      new_symbol.name=identifier;
      
      symbol_table.add(new_symbol);
      
      s_it=symbol_table.symbols.find(identifier);
      assert(s_it!=symbol_table.symbols.end());
    }
    else
    {
      // yes!
    }
  }
}

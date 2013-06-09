/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/prefix.h>

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
    
    // does it exist already in the destination symbol table?
    symbol_tablet::symbolst::const_iterator s_it=
      dest_symbol_table.symbols.find(identifier);
    
    if(s_it==dest_symbol_table.symbols.end())
    {
      assert(has_prefix(id2string(identifier), "java::"));
    
      // no, create the symbol
      symbolt new_symbol;
      new_symbol.name=identifier;
      new_symbol.is_type=true;
      new_symbol.type=class_typet();
      new_symbol.pretty_name=id2string(identifier).substr(6, std::string::npos);
      new_symbol.mode=ID_java;
      
      dest_symbol_table.add(new_symbol);
      
      s_it=dest_symbol_table.symbols.find(identifier);
      assert(s_it!=dest_symbol_table.symbols.end());
    }
    else
    {
      // yes!
    }
  }
  else if(type.id()==ID_pointer)
    typecheck_type(type.subtype());
  else if(type.id()==ID_array)
  {
    typecheck_type(type.subtype());
  }
  else if(type.id()==ID_code)
  {
    code_typet &code_type=to_code_type(type);
    typecheck_type(code_type.return_type());
    code_typet::parameterst &parameters=code_type.parameters();
    for(code_typet::parameterst::iterator
        it=parameters.begin(); it!=parameters.end(); it++)
      typecheck_type(it->type());
  }
}

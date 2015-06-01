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
    
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);
    
    // does it exist already in the symbol table?
    if(s_it!=symbol_table.symbols.end())
    {
      // yes, got it
      assert(s_it->second.is_type);
    }
    else
    {
      // No, not there. Must be class we failed to load.
      assert(has_prefix(id2string(identifier), "java::"));
      
      class_typet dummy_type;
      dummy_type.set(ID_incomplete_class, true);
      dummy_type.components().push_back(class_typet::componentt());
      dummy_type.components().back().type()=bool_typet();
      dummy_type.components().back().set_name("dummy");
    
      // no, create the symbol
      symbolt new_symbol;
      new_symbol.name=identifier;
      new_symbol.is_type=true;
      new_symbol.type=dummy_type;
      new_symbol.pretty_name=id2string(identifier).substr(6, std::string::npos);
      new_symbol.mode=ID_java;
      
      if(symbol_table.add(new_symbol))
        throw "failed to add an incomplete class symbol";
    }
  }
  else if(type.id()==ID_pointer)
  {
    typecheck_type(type.subtype());
  }
  else if(type.id()==ID_array)
  {
    typecheck_type(type.subtype());
    typecheck_expr(to_array_type(type).size());
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

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_type_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_type_symbol(symbolt &symbol)
{
  assert(symbol.is_type);
  
  typecheck_type(symbol.type);
}

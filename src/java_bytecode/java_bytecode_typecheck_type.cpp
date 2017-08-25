/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <util/std_types.h>

void java_bytecode_typecheckt::typecheck_type(typet &type)
{
  if(type.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_type(type).get_identifier();

    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);

    // must exist already in the symbol table
    if(s_it==symbol_table.symbols.end())
    {
      error() << "failed to find type symbol "<< identifier << eom;
      throw 0;
    }

    assert(s_it->second.is_type);
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

void java_bytecode_typecheckt::typecheck_type_symbol(symbolt &symbol)
{
  assert(symbol.is_type);

  typecheck_type(symbol.type);
}

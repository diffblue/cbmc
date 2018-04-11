/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <util/std_types.h>
#include <util/invariant.h>

void java_bytecode_typecheckt::typecheck_type(typet &type)
{
  if(type.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_type(type).get_identifier();

    auto type_symbol = symbol_table.lookup(identifier);
    DATA_INVARIANT(
      type_symbol, "symbol " + id2string(identifier) + " must exist already");
    DATA_INVARIANT(
      type_symbol->is_type,
      "symbol " + id2string(identifier) + " must exist already");
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
  DATA_INVARIANT(
    symbol.is_type, "symbol " + id2string(symbol.name) + " must exist already");

  symbol.mode = ID_java;
  typecheck_type(symbol.type);
}

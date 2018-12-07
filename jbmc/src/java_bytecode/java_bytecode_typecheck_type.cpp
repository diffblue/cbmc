/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <util/invariant.h>
#include <util/std_types.h>

void java_bytecode_typecheckt::typecheck_type(typet &type)
{
  if(type.id() == ID_struct_tag)
  {
    irep_idt identifier = to_struct_tag_type(type).get_identifier();

    auto type_symbol = symbol_table.lookup(identifier);
    DATA_INVARIANT(
      type_symbol, "symbol " + id2string(identifier) + " must exist already");
    DATA_INVARIANT(
      type_symbol->is_type,
      "symbol " + id2string(identifier) + " must be a type");
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
    java_method_typet &method_type = to_java_method_type(type);
    typecheck_type(method_type.return_type());

    java_method_typet::parameterst &parameters = method_type.parameters();

    for(java_method_typet::parameterst::iterator it = parameters.begin();
        it != parameters.end();
        it++)
      typecheck_type(it->type());
  }
}

void java_bytecode_typecheckt::typecheck_type_symbol(symbolt &symbol)
{
  DATA_INVARIANT(
    symbol.is_type, "symbol " + id2string(symbol.name) + " must be a type");

  symbol.mode = ID_java;
  typecheck_type(symbol.type);
}

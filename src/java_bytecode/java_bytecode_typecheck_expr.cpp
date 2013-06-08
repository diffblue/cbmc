/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "java_bytecode_typecheck.h"

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_expr(exprt &expr)
{ 
  if(expr.id()==ID_code)
    return typecheck_code(to_code(expr));
  
  // do operands recursively
  Forall_operands(it, expr)
    typecheck_expr(*it);

  if(expr.id()==ID_symbol)
    typecheck_expr_symbol(to_symbol_expr(expr));
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_expr_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_expr_symbol(symbol_exprt &expr)
{ 
  irep_idt identifier=expr.get_identifier();
  
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
    new_symbol.type=expr.type();
    
    symbol_table.add(new_symbol);
    
    s_it=symbol_table.symbols.find(identifier);
    assert(s_it!=symbol_table.symbols.end());
  }
  else
  {
    // yes!
  }
  
  const symbolt &symbol=s_it->second;

  // type the expression
  expr.type()=symbol.type;
}

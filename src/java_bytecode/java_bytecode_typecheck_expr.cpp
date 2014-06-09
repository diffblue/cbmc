/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/prefix.h>

#include <ansi-c/c_sizeof.h>

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
  else if(expr.id()==ID_side_effect)
  {
    const irep_idt &statement=to_side_effect_expr(expr).get_statement();
    if(statement==ID_java_new || statement==ID_java_new_array)
      typecheck_expr_java_new(to_side_effect_expr(expr));
  }
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_expr_java_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_expr_java_new(side_effect_exprt &expr)
{ 
  if(expr.get_statement()==ID_java_new_array)
    assert(expr.operands().size()==2);
  else
    assert(expr.operands().size()==1);

  typet &type=expr.type();
  typecheck_type(type);

  // we need to compute the size of the object to be allocated
  expr.op0()=c_sizeof(type.subtype(), ns);  
  expr.op0().set(ID_C_c_sizeof_type, type.subtype());
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
  
  // does it exist already in the destination symbol table?
  symbol_tablet::symbolst::const_iterator s_it=
    dest_symbol_table.symbols.find(identifier);
  
  if(s_it==dest_symbol_table.symbols.end())
  {
    assert(has_prefix(id2string(identifier), "java::"));
  
    // no, create the symbol
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.type=expr.type();
    new_symbol.base_name=expr.get(ID_C_base_name);
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
  
  const symbolt &symbol=s_it->second;

  // type the expression
  expr.type()=symbol.type;
}

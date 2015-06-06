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
  {
    typecheck_expr_symbol(to_symbol_expr(expr));
  }
  else if(expr.id()==ID_side_effect)
  {
    const irep_idt &statement=to_side_effect_expr(expr).get_statement();
    if(statement==ID_java_new)
      typecheck_expr_java_new(to_side_effect_expr(expr));
    else if(statement==ID_java_new_array)
      typecheck_expr_java_new_array(to_side_effect_expr(expr));
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
  assert(expr.operands().empty());
  typet &type=expr.type();
  typecheck_type(type);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_expr_java_new_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_expr_java_new_array(side_effect_exprt &expr)
{ 
  assert(expr.operands().size()>=1); // one per dimension
  typet &type=expr.type();
  typecheck_type(type);
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
    symbol_table.symbols.find(identifier);
  
  if(s_it==symbol_table.symbols.end())
  {
    #if 1
    assert(has_prefix(id2string(identifier), "java::"));
  
    // no, create the symbol
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.type=expr.type();
    new_symbol.base_name=expr.get(ID_C_base_name);
    new_symbol.pretty_name=id2string(identifier).substr(6, std::string::npos);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    
    if(new_symbol.type.id()==ID_code)
    {
      new_symbol.is_lvalue=false;
    }
    else
    {
      new_symbol.is_lvalue=true;
    }
    
    if(symbol_table.add(new_symbol))
      throw "failed to add expression symbol to symbol table";
    #else
    str << "failed to find expression symbol `"
        << identifier << "' in symbol table";
    throw 0;
    
    #endif
  }
  else
  {
    // yes!
    assert(!s_it->second.is_type);

    const symbolt &symbol=s_it->second;

    // type the expression
    expr.type()=symbol.type;
  }
}

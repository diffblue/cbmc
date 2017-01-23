/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/prefix.h>

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
    if(statement==ID_java_new)
      typecheck_expr_java_new(to_side_effect_expr(expr));
    else if(statement==ID_java_new_array)
      typecheck_expr_java_new_array(to_side_effect_expr(expr));
  }
  else if(expr.id()==ID_java_string_literal)
    typecheck_expr_java_string_literal(expr);
  else if(expr.id()==ID_member)
    typecheck_expr_member(to_member_expr(expr));
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

Function: java_bytecode_typecheckt::typecheck_expr_java_string_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_expr_java_string_literal(exprt &expr)
{
  const irep_idt value=expr.get(ID_value);

  // we create a symbol for these
  const irep_idt identifier="java::java.lang.String.Literal."+
    id2string(value);

  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(identifier);

  const symbol_typet string_type("java::java.lang.String");

  if(s_it==symbol_table.symbols.end())
  {
    // no, create the symbol
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.type=string_type;
    new_symbol.base_name="Literal";
    new_symbol.pretty_name=value;
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    new_symbol.is_lvalue=true;

    if(symbol_table.add(new_symbol))
    {
      error() << "failed to add string literal symbol to symbol table" << eom;
      throw 0;
    }
  }

  expr=address_of_exprt(
    symbol_exprt(identifier, string_type));
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
    {
      error() << "failed to add expression symbol to symbol table" << eom;
      throw 0;
    }
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

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_expr_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_expr_member(member_exprt &expr)
{
  // The member might be in a parent class, which we resolve here.
  const irep_idt component_name=expr.get_component_name();

  while(1)
  {
    if(ns.follow(expr.struct_op().type()).id()!=ID_struct)
      break; // give up

    const struct_typet &struct_type=
      to_struct_type(ns.follow(expr.struct_op().type()));

    if(struct_type.has_component(component_name))
      return; // done

    // look at parent
    const struct_typet::componentst &components=
      struct_type.components();

    if(components.empty())
      break; // give up

    const struct_typet::componentt &c=components.front();

    member_exprt m(expr.struct_op(), c.get_name(), c.type());
    m.add_source_location()=expr.source_location();

    expr.struct_op()=m;
  }

  warning().source_location=expr.source_location();
  warning() << "failed to find field `"
            << component_name << "` in class hierarchy" << eom;

  exprt compound(expr.compound());
  bool previous_dereference(true);

  // We will search for the dereference in the member expr
  while(compound.id()!=ID_dereference) 
  {
    if(compound.id()==ID_member) 
    {
      // If it's a member we go deeper
      compound=to_member_expr(compound).compound();
    }
    else 
    {
      // Otherwise, we give up
      previous_dereference=false;  
      break; 
    }
  }


   // Create a non-det of same type
  side_effect_expr_nondett nondet(expr.type());

  if(previous_dereference) 
  {
    assert(compound.id()==ID_dereference);
    // Attach the dereference
    nondet.set("previous-dereference", compound); 
  }

  // We replace by the non-det
  expr.swap(nondet);
}

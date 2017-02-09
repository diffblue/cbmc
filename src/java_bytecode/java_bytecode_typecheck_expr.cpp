/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/prefix.h>

#include "java_bytecode_typecheck.h"
#include "java_pointer_casts.h"

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

  if(expr.id()==ID_typecast && expr.type().id()==ID_pointer)
    expr=make_clean_pointer_cast(expr, expr.type(), ns);

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

void java_bytecode_typecheckt::typecheck_expr_java_new_array(
  side_effect_exprt &expr)
{
  assert(expr.operands().size()>=1); // one per dimension
  typet &type=expr.type();
  typecheck_type(type);
}

static void escape_non_alnum(std::string &toescape)
{
  for(auto &ch : toescape)
    if(!isalnum(ch))
      ch='_';
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
  const symbol_typet string_type("java::java.lang.String");

  auto findit=string_literal_to_symbol_name.find(value);
  if(findit!=string_literal_to_symbol_name.end())
  {
    expr=symbol_exprt(findit->second, pointer_typet(string_type));
    return;
  }

  // Create a new symbol:
  std::ostringstream identifier_str;
  std::string escaped=id2string(value);
  escape_non_alnum(escaped);
  identifier_str << "java::java.lang.String.Literal." << escaped;
  // Avoid naming clashes by virtue of escaping:
  // NOTE this increments the count stored in the map.
  size_t unique_num=++(escaped_string_literal_count[identifier_str.str()]);
  if(unique_num!=1)
    identifier_str << unique_num;

  irep_idt identifier_id=identifier_str.str();
  string_literal_to_symbol_name.insert(std::make_pair(value, identifier_id));

  symbolt new_symbol;
  new_symbol.name=identifier_id;
  new_symbol.type=pointer_typet(string_type);
  new_symbol.base_name="Literal";
  new_symbol.pretty_name=value;
  new_symbol.mode=ID_java;
  new_symbol.is_type=false;
  new_symbol.is_lvalue=true;
  new_symbol.is_static_lifetime=true; // These are basically const global data.

  if(symbol_table.add(new_symbol))
  {
    error() << "failed to add string literal symbol to symbol table" << eom;
    throw 0;
  }

  expr=new_symbol.symbol_expr();
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
  // The member might be in a parent class or an opaque class, which we resolve
  // here.
  const irep_idt component_name=expr.get_component_name();

  while(1)
  {
    typet base_type(ns.follow(expr.struct_op().type()));

    if(base_type.id()!=ID_struct)
      break; // give up

    struct_typet &struct_type=
      to_struct_type(base_type);

    if(struct_type.has_component(component_name))
      return; // done

    // look at parent
    struct_typet::componentst &components=
      struct_type.components();

    if(struct_type.get_bool(ID_incomplete_class))
    {
      // member doesn't exist. In this case struct_type should be an opaque
      // stub, and we'll add the member to it.
      symbolt &symbol_table_type=
        symbol_table.lookup("java::"+id2string(struct_type.get_tag()));
      auto &add_to_components=
        to_struct_type(symbol_table_type.type).components();
      add_to_components
        .push_back(struct_typet::componentt(component_name, expr.type()));
      add_to_components.back().set_base_name(component_name);
      add_to_components.back().set_pretty_name(component_name);
      return;
    }

    if(components.empty())
      break;

    const struct_typet::componentt &c=components.front();

    member_exprt m(expr.struct_op(), c.get_name(), c.type());
    m.add_source_location()=expr.source_location();

    expr.struct_op()=m;
  }

  warning().source_location=expr.source_location();
  warning() << "failed to find field `"
            << component_name << "` in class hierarchy" << eom;

  // We replace by a non-det of same type
  side_effect_expr_nondett nondet(expr.type());
  expr.swap(nondet);
}

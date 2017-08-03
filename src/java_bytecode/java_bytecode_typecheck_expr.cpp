/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <iomanip>

#include <util/std_expr.h>
#include <util/prefix.h>
#include <util/arith_tools.h>
#include <util/unicode.h>

#include <linking/zero_initializer.h>

#include "java_pointer_casts.h"
#include "java_types.h"
#include "java_utils.h"

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

void java_bytecode_typecheckt::typecheck_expr_java_new(side_effect_exprt &expr)
{
  assert(expr.operands().empty());
  typet &type=expr.type();
  typecheck_type(type);
}

void java_bytecode_typecheckt::typecheck_expr_java_new_array(
  side_effect_exprt &expr)
{
  assert(expr.operands().size()>=1); // one per dimension
  typet &type=expr.type();
  typecheck_type(type);
}

static std::string escape_non_alnum(const std::string &toescape)
{
  std::ostringstream escaped;
  for(auto &ch : toescape)
  {
    if(ch=='_')
      escaped << "__";
    else if(isalnum(ch))
      escaped << ch;
    else
      escaped << '_'
              << std::hex
              << std::setfill('0')
              << std::setw(2)
              << (unsigned int)ch;
  }
  return escaped.str();
}

/// Convert UCS-2 or UTF-16 to an array expression.
/// \par parameters: `in`: wide string to convert
/// \return Returns a Java char array containing the same wchars.
static array_exprt utf16_to_array(const std::wstring &in)
{
  const auto jchar=java_char_type();
  array_exprt ret(array_typet(jchar, infinity_exprt(java_int_type())));
  for(const auto c : in)
    ret.copy_to_operands(from_integer(c, jchar));
  return ret;
}

void java_bytecode_typecheckt::typecheck_expr_java_string_literal(exprt &expr)
{
  const irep_idt value=expr.get(ID_value);
  const symbol_typet string_type("java::java.lang.String");

  std::string escaped_symbol_name=JAVA_STRING_LITERAL_PREFIX ".";
  escaped_symbol_name+=escape_non_alnum(id2string(value));

  auto findit=symbol_table.symbols.find(escaped_symbol_name);
  if(findit!=symbol_table.symbols.end())
  {
    expr=address_of_exprt(findit->second.symbol_expr());
    return;
  }

  // Create a new symbol:
  symbolt new_symbol;
  new_symbol.name=escaped_symbol_name;
  new_symbol.type=string_type;
  new_symbol.base_name="Literal";
  new_symbol.pretty_name=value;
  new_symbol.mode=ID_java;
  new_symbol.is_type=false;
  new_symbol.is_lvalue=true;
  new_symbol.is_static_lifetime=true; // These are basically const global data.

  // Regardless of string refinement setting, at least initialize
  // the literal with @clsid = String and @lock = false:
  symbol_typet jlo_symbol("java::java.lang.Object");
  const auto &jlo_struct=to_struct_type(ns.follow(jlo_symbol));
  struct_exprt jlo_init(jlo_symbol);
  const auto &jls_struct=to_struct_type(ns.follow(string_type));

  jlo_init.copy_to_operands(
    constant_exprt(
      "java::java.lang.String",
      jlo_struct.components()[0].type()));
  jlo_init.copy_to_operands(
    from_integer(
      0,
      jlo_struct.components()[1].type()));

  // If string refinement *is* around, populate the actual
  // contents as well:
  if(string_refinement_enabled)
  {
    struct_exprt literal_init(new_symbol.type);
    literal_init.move_to_operands(jlo_init);

    // Initialize the string with a constant utf-16 array:
    symbolt array_symbol;
    array_symbol.name=escaped_symbol_name+"_constarray";
    array_symbol.type=array_typet(
      java_char_type(), infinity_exprt(java_int_type()));
    array_symbol.base_name="Literal_constarray";
    array_symbol.pretty_name=value;
    array_symbol.mode=ID_java;
    array_symbol.is_type=false;
    array_symbol.is_lvalue=true;
    // These are basically const global data:
    array_symbol.is_static_lifetime=true;
    array_symbol.is_state_var=true;
    auto literal_array=utf16_to_array(
      utf8_to_utf16_little_endian(id2string(value)));
    array_symbol.value=literal_array;

    if(symbol_table.add(array_symbol))
      throw "failed to add constarray symbol to symbol table";

    literal_init.copy_to_operands(
      from_integer(literal_array.operands().size(),
                   jls_struct.components()[1].type()));
    literal_init.copy_to_operands(
      address_of_exprt(array_symbol.symbol_expr()));

    new_symbol.value=literal_init;
  }
  else if(jls_struct.components().size()>=1 &&
          jls_struct.components()[0].get_name()=="@java.lang.Object")
  {
    // Case where something defined java.lang.String, so it has
    // a proper base class (always java.lang.Object in practical
    // JDKs seen so far)
    struct_exprt literal_init(new_symbol.type);
    literal_init.move_to_operands(jlo_init);
    for(const auto &comp : jls_struct.components())
    {
      if(comp.get_name()=="@java.lang.Object")
        continue;
      // Other members of JDK's java.lang.String we don't understand
      // without string-refinement. Just zero-init them; consider using
      // test-gen-like nondet object trees instead.
      literal_init.copy_to_operands(
        zero_initializer(comp.type(), expr.source_location(), ns));
    }
    new_symbol.value=literal_init;
  }
  else if(jls_struct.get_bool(ID_incomplete_class))
  {
    // Case where java.lang.String was stubbed, and so directly defines
    // @class_identifier and @lock:
    new_symbol.value=jlo_init;
  }

  if(symbol_table.add(new_symbol))
  {
    error() << "failed to add string literal symbol to symbol table" << eom;
    throw 0;
  }

  expr=address_of_exprt(new_symbol.symbol_expr());
}

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

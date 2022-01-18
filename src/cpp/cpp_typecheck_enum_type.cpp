/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_enum_type.h"

void cpp_typecheckt::typecheck_enum_body(symbolt &enum_symbol)
{
  c_enum_typet &c_enum_type=to_c_enum_type(enum_symbol.type);

  exprt &body=static_cast<exprt &>(c_enum_type.add(ID_body));
  irept::subt &components=body.get_sub();

  c_enum_tag_typet enum_tag_type(enum_symbol.name);

  mp_integer i=0;

  for(auto &component : components)
  {
    const irep_idt &name = component.get(ID_name);

    if(component.find(ID_value).is_not_nil())
    {
      exprt &value = static_cast<exprt &>(component.add(ID_value));
      typecheck_expr(value);
      implicit_typecast(value, c_enum_type.underlying_type());
      make_constant(value);
      if(to_integer(to_constant_expr(value), i))
      {
        error().source_location=value.find_source_location();
        error() << "failed to produce integer for enum constant" << eom;
        throw 0;
      }
    }

    exprt value_expr = from_integer(i, c_enum_type.underlying_type());
    value_expr.type()=enum_tag_type; // override type

    symbolt symbol;

    symbol.name=id2string(enum_symbol.name)+"::"+id2string(name);
    symbol.base_name=name;
    symbol.value=value_expr;
    symbol.location = static_cast<const source_locationt &>(
      component.find(ID_C_source_location));
    symbol.mode = enum_symbol.mode;
    symbol.module=module;
    symbol.type=enum_tag_type;
    symbol.is_type=false;
    symbol.is_macro=true;
    symbol.is_file_local = true;
    symbol.is_thread_local = true;

    symbolt *new_symbol;
    if(symbol_table.move(symbol, new_symbol))
    {
      error().source_location=symbol.location;
      error() << "cpp_typecheckt::typecheck_enum_body: "
              << "symbol_table.move() failed" << eom;
      throw 0;
    }

    cpp_idt &scope_identifier=
      cpp_scopes.put_into_scope(*new_symbol);

    scope_identifier.id_class=cpp_idt::id_classt::SYMBOL;

    ++i;
  }
}

void cpp_typecheckt::typecheck_enum_type(typet &type)
{
  // first save qualifiers
  c_qualifierst qualifiers;
  qualifiers.read(type);

  cpp_enum_typet &enum_type=to_cpp_enum_type(type);
  bool anonymous=!enum_type.has_tag();
  irep_idt base_name;

  cpp_save_scopet save_scope(cpp_scopes);

  if(anonymous)
  {
    // we fabricate a tag based on the enum constants contained
    base_name=enum_type.generate_anon_tag();
  }
  else
  {
    const cpp_namet &tag=enum_type.tag();

    cpp_template_args_non_tct template_args;
    template_args.make_nil();

    cpp_typecheck_resolvet resolver(*this);
    resolver.resolve_scope(tag, base_name, template_args);
  }

  bool has_body=enum_type.has_body();
  bool tag_only_declaration=enum_type.get_tag_only_declaration();

  cpp_scopet &dest_scope=
    tag_scope(base_name, has_body, tag_only_declaration);

  const irep_idt symbol_name=
    dest_scope.prefix+"tag-"+id2string(base_name);

  // check if we have it

  symbol_tablet::symbolst::const_iterator previous_symbol=
    symbol_table.symbols.find(symbol_name);

  if(previous_symbol!=symbol_table.symbols.end())
  {
    // we do!

    const symbolt &symbol=previous_symbol->second;

    if(has_body)
    {
      error().source_location=type.source_location();
      error() << "error: enum symbol '" << base_name
              << "' declared previously\n"
              << "location of previous definition: " << symbol.location << eom;
      throw 0;
    }
  }
  else if(
    has_body ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    std::string pretty_name=
      cpp_scopes.current_scope().prefix+id2string(base_name);

    // C++11 enumerations have an underlying type,
    // which defaults to int.
    // enums without underlying type may be 'packed'.
    if(type.subtype().is_nil())
      type.subtype()=signed_int_type();
    else
    {
      typecheck_type(type.subtype());
      if(
        type.subtype().id() != ID_signedbv &&
        type.subtype().id() != ID_unsignedbv &&
        type.subtype().id() != ID_c_bool)
      {
        error().source_location=type.source_location();
        error() << "underlying type must be integral" << eom;
        throw 0;
      }
    }

    symbolt symbol;

    symbol.name=symbol_name;
    symbol.base_name=base_name;
    symbol.value.make_nil();
    symbol.location=type.source_location();
    symbol.mode=ID_cpp;
    symbol.module=module;
    symbol.type.swap(type);
    symbol.is_type=true;
    symbol.is_macro=false;
    symbol.pretty_name=pretty_name;

    // move early, must be visible before doing body
    symbolt *new_symbol;
    if(symbol_table.move(symbol, new_symbol))
    {
      error().source_location=symbol.location;
      error() << "cpp_typecheckt::typecheck_enum_type: "
              << "symbol_table.move() failed" << eom;
      throw 0;
    }

    // put into scope
    cpp_idt &scope_identifier=
      cpp_scopes.put_into_scope(*new_symbol, dest_scope);

    scope_identifier.id_class=cpp_idt::id_classt::CLASS;
    scope_identifier.is_scope = true;

    cpp_save_scopet save_scope_before_enum_typecheck(cpp_scopes);

    if(new_symbol->type.get_bool(ID_C_class))
      cpp_scopes.go_to(scope_identifier);

    if(has_body)
      typecheck_enum_body(*new_symbol);
  }
  else
  {
    error().source_location=type.source_location();
    error() << "use of enum '" << base_name << "' without previous declaration"
            << eom;
    throw 0;
  }

  // create enum tag expression, and add the qualifiers
  type=c_enum_tag_typet(symbol_name);
  qualifiers.write(type);
}

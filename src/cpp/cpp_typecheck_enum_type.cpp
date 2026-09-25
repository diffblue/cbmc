/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_enum_type.h"
#include "cpp_typecheck.h"

void cpp_typecheckt::typecheck_enum_body(
  symbolt &enum_symbol,
  bool underlying_defaulted)
{
  c_enum_typet &c_enum_type=to_c_enum_type(enum_symbol.type);

  exprt &body=static_cast<exprt &>(c_enum_type.add(ID_body));
  irept::subt &components=body.get_sub();

  c_enum_tag_typet enum_tag_type(enum_symbol.name);

  mp_integer i=0;

  // Range of enumerator values and the created enumerator symbols,
  // for the GCC packed-enum extension below.
  mp_integer min_value = 0, max_value = 0;
  std::vector<std::pair<irep_idt, mp_integer>> made_enumerators;

  for(auto &component : components)
  {
    const irep_idt &name = component.get(ID_name);

    if(component.find(ID_value).is_not_nil())
    {
      exprt &value = static_cast<exprt &>(component.add(ID_value));
      // [dcl.enum]: an enumerator value is a constant expression.
      constant_expression_contextt constant_expression_guard{*this};
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

    if(i < min_value)
      min_value = i;
    if(i > max_value)
      max_value = i;

    exprt value_expr = from_integer(i, c_enum_type.underlying_type());
    value_expr.type()=enum_tag_type; // override type

    symbolt symbol{
      id2string(enum_symbol.name) + "::" + id2string(name),
      enum_tag_type,
      enum_symbol.mode};
    symbol.base_name=name;
    symbol.value=value_expr;
    symbol.location = static_cast<const source_locationt &>(
      component.find(ID_C_source_location));
    symbol.module=module;
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

    made_enumerators.emplace_back(new_symbol->name, i);

    cpp_idt &scope_identifier=
      cpp_scopes.put_into_scope(*new_symbol);

    scope_identifier.id_class=cpp_idt::id_classt::SYMBOL;

    // N5008 [dcl.enum]/12: an UNSCOPED enumeration's enumerators can
    // also be referred to with the scope-resolution syntax
    // (`kindt::CALL`, C++11).  The current scope here is the ENCLOSING
    // scope for an unscoped enum (only `enum class` switches to the
    // enum's own scope before this function), so additionally register
    // the enumerator in the enum's scope; without this,
    // `resolve_scope` correctly entered `kindt::` but the qualified
    // lookup of the enumerator found nothing and the whole expression
    // failed ("found no match" with a nil-typed argument when it was a
    // member-call argument).
    if(!enum_symbol.type.get_bool(ID_C_class))
    {
      auto scope_it = cpp_scopes.id_map.find(enum_symbol.name);
      if(
        scope_it != cpp_scopes.id_map.end() && scope_it->second->is_scope &&
        &*scope_it->second != &cpp_scopes.current_scope())
      {
        cpp_idt &in_enum_scope = cpp_scopes.put_into_scope(
          *new_symbol, static_cast<cpp_scopet &>(*scope_it->second));
        in_enum_scope.id_class = cpp_idt::id_classt::SYMBOL;
      }
    }

    ++i;
  }

  // GCC's `enum __attribute__((__packed__))` extension, honoured by
  // the C front end (c_typecheck_type.cpp): with no enumeration-base
  // written, the underlying type is the SMALLEST sufficient integer
  // type.  N5008 [dcl.enum]/8 leaves the underlying type
  // implementation-defined in that case, and matching the platform
  // compiler is what makes sizeof agree (user-reported: 1-byte
  // instruction fields via packed enums in packed structs).  The
  // enumerator symbols were created against the provisional `int` so
  // that later enumerators can reference earlier ones ([dcl.enum]/5);
  // re-type their stored values to the final width.
  if(underlying_defaulted && c_enum_type.get_bool(ID_C_packed))
  {
    to_type_with_subtype(c_enum_type).subtype() =
      enum_underlying_type(min_value, max_value, true);
    for(const auto &e : made_enumerators)
    {
      symbolt &esym = symbol_table.get_writeable_ref(e.first);
      exprt v = from_integer(e.second, c_enum_type.underlying_type());
      v.type() = enum_tag_type;
      esym.value = std::move(v);
    }
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

  symbol_table_baset::symbolst::const_iterator previous_symbol =
    symbol_table.symbols.find(symbol_name);

  if(previous_symbol!=symbol_table.symbols.end())
  {
    // we do!

    const symbolt &symbol=previous_symbol->second;

    if(has_body)
    {
      // Allow defining an enum that was previously forward-declared
      if(
        symbol.type.id() == ID_c_enum_tag ||
        symbol.type.get(ID_C_incomplete) == "1" ||
        !symbol.type.find(ID_body).is_not_nil())
      {
        // Replace the forward declaration with the full definition.
        symbolt &writable = symbol_table.get_writeable_ref(symbol_name);
        writable.type = enum_type;

        if(writable.type.add_subtype().is_nil())
          writable.type.add_subtype() = signed_int_type();
        else
          typecheck_type(to_type_with_subtype(writable.type).subtype());

        // Find the existing scope entry for this enum
        cpp_scopet::id_sett id_set =
          cpp_scopes.current_scope().lookup(base_name, cpp_scopet::SCOPE_ONLY);
        cpp_idt *scope_id = nullptr;
        for(auto *id : id_set)
        {
          if(id->identifier == symbol_name)
          {
            scope_id = &*id;
            break;
          }
        }

        if(scope_id)
        {
          cpp_save_scopet save2(cpp_scopes);
          if(writable.type.get_bool(ID_C_class))
            cpp_scopes.go_to(*scope_id);
          typecheck_enum_body(writable, false);
        }
      }
      else
      {
        error().source_location = type.source_location();
        error() << "enum symbol '" << base_name << "' declared previously\n"
                << "location of previous definition: " << symbol.location
                << eom;
        throw 0;
      }
    }
  }
  else if(
    has_body ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO ||
    type.add_subtype()
      .is_not_nil() ||         // forward-declared enum with underlying type
    type.get_bool(ID_C_class)) // C++11: forward-declared `enum class`
  {
    std::string pretty_name=
      cpp_scopes.current_scope().prefix+id2string(base_name);

    // C++11 enumerations have an underlying type,
    // which defaults to int.
    // enums without underlying type may be 'packed'.
    // Whether the program wrote no enumeration-base; only then may
    // GCC's packed-enum extension shrink the underlying type (see
    // typecheck_enum_body).  Scoped enums always have a FIXED
    // underlying type (int if unspecified, N5008 [dcl.enum]/5), which
    // the packed attribute does not affect.
    bool underlying_defaulted = false;
    if(type.add_subtype().is_nil())
    {
      type.add_subtype() = signed_int_type();
      underlying_defaulted = !type.get_bool(ID_C_class);
    }
    else
    {
      typecheck_type(to_type_with_subtype(type).subtype());
      if(
        to_type_with_subtype(type).subtype().id() != ID_signedbv &&
        to_type_with_subtype(type).subtype().id() != ID_unsignedbv &&
        to_type_with_subtype(type).subtype().id() != ID_c_bool)
      {
        error().source_location=type.source_location();
        error() << "underlying type must be integral" << eom;
        throw 0;
      }
    }

    type_symbolt symbol{symbol_name, type, ID_cpp};
    symbol.base_name=base_name;
    symbol.value.make_nil();
    symbol.location=type.source_location();
    symbol.module=module;
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
      typecheck_enum_body(*new_symbol, underlying_defaulted);
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

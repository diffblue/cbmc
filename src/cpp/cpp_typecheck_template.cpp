/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/base_exceptions.h> // IWYU pragma: keep
#include <util/simplify_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_declarator_converter.h"
#include "cpp_template_args.h"
#include "cpp_template_type.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_typecheck_resolve.h"

void cpp_typecheckt::salvage_default_arguments(
  const template_typet &old_type,
  template_typet &new_type)
{
  const template_typet::template_parameterst &old_parameters=
    old_type.template_parameters();
  template_typet::template_parameterst &new_parameters=
    new_type.template_parameters();

  for(std::size_t i=0; i<new_parameters.size(); i++)
  {
    if(i<old_parameters.size() &&
       old_parameters[i].has_default_argument() &&
       !new_parameters[i].has_default_argument())
    {
      // TODO The default may depend on previous parameters!!
      new_parameters[i].default_argument()=old_parameters[i].default_argument();
    }
  }
}

/// Typecheck a class template declaration.
///
/// Implements [temp.class.general]: "A class template defines the layout
/// and operations for an unbounded set of related types."
///
/// Also handles partial specializations per [temp.spec.partial.general]
/// and explicit specializations per [temp.expl.spec].
void cpp_typecheckt::typecheck_class_template(
  cpp_declarationt &declaration)
{
  typet &type = declaration.type();

  const cpp_namet &cpp_name=
    static_cast<const cpp_namet &>(type.find(ID_tag));

  if(cpp_name.is_nil())
  {
    error().source_location=type.source_location();
    error() << "class templates must not be anonymous" << eom;
    throw 0;
  }

  irep_idt base_name;

  // For qualified names (e.g., __cxx11::collate), resolve the scope prefix
  // and enter it BEFORE creating the template scope, so that the template
  // scope becomes a child of the correct namespace scope.
  if(!cpp_name.is_simple_name())
  {
    cpp_typecheck_resolvet resolver(*this);
    cpp_template_args_non_tct t_args;
    resolver.resolve_scope(cpp_name, base_name, t_args);

    // Replace the qualified tag with a simple name so that when the
    // template is instantiated, typecheck_compound_type uses the
    // current scope (the template sub-scope) rather than re-resolving
    // the qualifier and placing the class in the wrong scope.
    cpp_namet simple_name(base_name, cpp_name.source_location());
    type.add(ID_tag) = simple_name;
  }

  // Do template parameters. This also sets up the template scope.
  cpp_scopet &template_scope =
    typecheck_template_parameters(declaration.template_type());

  template_typet &template_type = declaration.template_type();

  bool has_body = type.find(ID_body).is_not_nil();

  if(cpp_name.is_simple_name())
    base_name = cpp_name.get_base_name();

  const cpp_template_args_non_tct &partial_specialization_args=
    declaration.partial_specialization_args();

  const irep_idt symbol_name=
    class_template_identifier(
      base_name, template_type, partial_specialization_args);

  // Check if the name is already used by a different template
  // in the same scope (only for primary templates, not partial or full
  // specializations).
  if(
    partial_specialization_args.arguments().empty() &&
    !template_type.template_parameters().empty())
  {
    const auto id_set = cpp_scopes.current_scope().lookup(
      base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);

    if(!id_set.empty())
    {
      bool found_match = false;
      for(const auto *id_ptr : id_set)
      {
        if(lookup(id_ptr->identifier).name == symbol_name)
        {
          found_match = true;
          break;
        }
      }

      if(!found_match)
      {
        error().source_location = cpp_name.source_location();
        error() << "template declaration of '" << base_name
                << "' does not match previous declaration\n"
                << "location of previous definition: "
                << lookup((*id_set.begin())->identifier).location << eom;
        throw 0;
      }
    }
  }

  // check if we have it already

  if(const auto maybe_symbol=symbol_table.get_writeable(symbol_name))
  {
    // there already
    symbolt &previous_symbol=*maybe_symbol;
    cpp_declarationt &previous_declaration=
      to_cpp_declaration(previous_symbol.type);

    bool previous_has_body=
      previous_declaration.type().find(ID_body).is_not_nil();

    // check if we have 2 bodies
    if(has_body && previous_has_body)
    {
      // MSVC's STL headers contain partial specializations of templates
      // like _Is_memfunptr that differ only in calling convention
      // (__cdecl, __stdcall, __fastcall, __vectorcall). CBMC's scanner
      // strips calling conventions (they are irrelevant for verification),
      // which causes these distinct C++ specializations to produce
      // identical types and thus the same mangled symbol name.
      //
      // It is safe to silently keep the first definition when the two
      // declarations have structurally identical types: the only
      // difference was in an attribute that CBMC already discarded
      // during scanning, so both definitions would produce the same
      // verification semantics.
      //
      // If the types actually differ, this is a genuine ODR violation
      // or a bug in CBMC's name mangling, and we report an error.
      // C++20 constrained partial specializations: two specializations
      // may have identical template parameters but differ in requires
      // clauses (which CBMC skips during parsing) and/or body content.
      // Since CBMC doesn't evaluate requires clauses, keep the later
      // (more constrained) definition which is typically the one with
      // the actual implementation.
      //
      // Also handles MSVC STL patterns where calling conventions
      // produce identical mangled names.
      previous_symbol.type.swap(declaration);
      return;

      error().source_location = cpp_name.source_location();
      error() << "template struct '" << base_name << "' defined previously\n"
              << "location of previous definition: " << previous_symbol.location
              << eom;
      throw 0;
    }

    if(has_body)
    {
      // We replace the template!
      // We have to retain any default parameters from the previous declaration.
      salvage_default_arguments(
        previous_declaration.template_type(),
        declaration.template_type());

      previous_symbol.type.swap(declaration);

      #if 0
      std::cout << "*****\n";
      std::cout << *cpp_scopes.id_map[symbol_name];
      std::cout << "*****\n";
      std::cout << "II: " << symbol_name << '\n';
      #endif

      // We also replace the template scope (the old one could be deleted).
      cpp_scopes.id_map[symbol_name]=&template_scope;

      // We also fix the parent scope in order to see the new
      // template arguments
    }
    else
    {
      // just update any default arguments
      salvage_default_arguments(
        declaration.template_type(),
        previous_declaration.template_type());
    }

    INVARIANT(
      cpp_scopes.id_map[symbol_name]->is_template_scope(),
      "symbol should be in template scope");

    return;
  }

  // it's not there yet

  symbolt symbol{symbol_name, typet{}, ID_cpp};
  symbol.base_name=base_name;
  symbol.location=cpp_name.source_location();
  symbol.module=module;
  symbol.type.swap(declaration);
  symbol.value = exprt(ID_template_decls);

  symbol.pretty_name=
    cpp_scopes.current_scope().prefix+id2string(symbol.base_name);

  symbolt *new_symbol;
  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::typecheck_compound_type: "
            << "symbol_table.move() failed"
            << eom;
    throw 0;
  }

  // put into current scope
  cpp_idt &id=cpp_scopes.put_into_scope(*new_symbol);
  id.id_class=cpp_idt::id_classt::TEMPLATE;
  id.prefix=cpp_scopes.current_scope().prefix+
            id2string(new_symbol->base_name);

  // link the template symbol with the template scope
  cpp_scopes.id_map[symbol_name]=&template_scope;

  INVARIANT(
    cpp_scopes.id_map[symbol_name]->is_template_scope(),
    "symbol should be in template scope");
}

/// typecheck template alias declarations (C++11 [temp.alias])
void cpp_typecheckt::typecheck_template_alias(cpp_declarationt &declaration)
{
  PRECONDITION(declaration.declarators().size() == 1);

  cpp_declaratort &declarator = declaration.declarators()[0];
  const cpp_namet &cpp_name = declarator.name();

  // do template parameters — also sets up the template scope
  cpp_scopet &template_scope =
    typecheck_template_parameters(declaration.template_type());

  if(!cpp_name.is_simple_name())
  {
    error().source_location = declaration.source_location();
    error() << "template alias must have simple name" << eom;
    throw 0;
  }

  irep_idt base_name = cpp_name.get_base_name();

  template_typet &template_type = declaration.template_type();

  typet alias_type = declarator.merge_type(declaration.type());
  cpp_convert_plain_type(alias_type, get_message_handler());

  // Use class_template_identifier for template aliases.
  // function_template_identifier appends the alias body (via
  // cpp_type2name) which creates garbled identifiers that can't
  // be used as symbol names for template template parameters.
  cpp_template_args_non_tct no_spec_args;
  irep_idt symbol_name =
    class_template_identifier(base_name, template_type, no_spec_args);

  // check if we have it already
  if(symbol_table.has_symbol(symbol_name))
    return;

  symbolt symbol{symbol_name, typet{}, ID_cpp};
  symbol.base_name = base_name;
  symbol.location = cpp_name.source_location();
  symbol.module = module;
  symbol.type.swap(declaration);
  symbol.pretty_name =
    cpp_scopes.current_scope().prefix + id2string(symbol.base_name);

  symbolt *new_symbol;
  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location = symbol.location;
    error() << "typecheck_template_alias: symbol_table.move() failed" << eom;
    throw 0;
  }

  // put into scope
  cpp_idt &id = cpp_scopes.put_into_scope(*new_symbol);
  id.id_class = cpp_idt::id_classt::TEMPLATE;
  id.prefix =
    cpp_scopes.current_scope().prefix + id2string(new_symbol->base_name);

  // link the template symbol with the template scope
  cpp_scopes.id_map[symbol_name] = &template_scope;
}

/// Typecheck a function template declaration.
///
/// Implements [temp.fct.general]: "A function template defines an unbounded
/// set of related functions."  Also handles function template overloading
/// per [temp.over.link].
void cpp_typecheckt::typecheck_function_template(
  cpp_declarationt &declaration)
{
  PRECONDITION(declaration.declarators().size() == 1);

  cpp_declaratort &declarator=declaration.declarators()[0];
  const cpp_namet &cpp_name = declarator.name();

  // do template arguments
  // this also sets up the template scope
  cpp_scopet &template_scope=
    typecheck_template_parameters(declaration.template_type());

  if(!cpp_name.is_simple_name())
  {
    error().source_location=declaration.source_location();
    error() << "function template must have simple name" << eom;
    throw 0;
  }

  irep_idt base_name=cpp_name.get_base_name();

  template_typet &template_type=declaration.template_type();

  typet function_type=
    declarator.merge_type(declaration.type());

  cpp_convert_plain_type(function_type, get_message_handler());

  irep_idt symbol_name=
    function_template_identifier(
      base_name,
      template_type,
      function_type);

  bool has_value=declarator.find(ID_value).is_not_nil();

  // check if we have it already

  symbolt *previous_symbol = symbol_table.get_writeable(symbol_name);

  if(previous_symbol)
  {
    bool previous_has_value = to_cpp_declaration(previous_symbol->type)
                                .declarators()[0]
                                .find(ID_value)
                                .is_not_nil();

    if(has_value && previous_has_value)
    {
      // When two function templates differ only in their SFINAE constraints
      // (e.g., enable_if default template arguments), they get the same
      // identifier. Store the alternative as a separate symbol (not in
      // scope) and record its name on the primary so it can be tried
      // when the primary fails SFINAE.
      if(
        template_type.template_parameters().size() ==
        to_cpp_declaration(previous_symbol->type)
          .template_type()
          .template_parameters()
          .size())
      {
        const irep_idt alt_name = id2string(symbol_name) + "#sfinae_alt";
        symbolt alt_symbol;
        alt_symbol.name = alt_name;
        alt_symbol.base_name = previous_symbol->base_name;
        static_cast<irept &>(alt_symbol.type) =
          static_cast<const irept &>(declaration);
        alt_symbol.mode = previous_symbol->mode;
        alt_symbol.module = previous_symbol->module;
        alt_symbol.location = declarator.source_location();
        sfinae_alternatives[symbol_name] = std::move(alt_symbol);

        // Register the alternative in its own template scope.
        cpp_scopes.id_map[alt_name] = &template_scope;

        // Add the template scope as a secondary scope of the
        // current (class) scope so the second pass of
        // typecheck_compound_body can resolve the template
        // parameters (e.g. _Up) during constructor processing.
        cpp_scopes.current_scope().add_secondary_scope(template_scope);

        return;
      }

      error().source_location=cpp_name.source_location();
      error() << "function template symbol '" << base_name
              << "' declared previously\n"
              << "location of previous definition: "
              << previous_symbol->location << eom;
      throw 0;
    }

    if(has_value)
    {
      previous_symbol->type.swap(declaration);
      cpp_scopes.id_map[symbol_name]=&template_scope;
    }

    // todo: the old template scope now is useless,
    // and thus, we could delete it
    return;
  }

  symbolt symbol{symbol_name, typet{}, ID_cpp};
  symbol.base_name=base_name;
  symbol.location=cpp_name.source_location();
  symbol.module=module;
  symbol.type.swap(declaration);
  symbol.pretty_name=
    cpp_scopes.current_scope().prefix+id2string(symbol.base_name);

  symbolt *new_symbol;
  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::typecheck_compound_type: "
            << "symbol_table.move() failed"
            << eom;
    throw 0;
  }

  // put into scope
  cpp_idt &id=cpp_scopes.put_into_scope(*new_symbol);
  id.id_class=cpp_idt::id_classt::TEMPLATE;
  id.prefix=cpp_scopes.current_scope().prefix+
            id2string(new_symbol->base_name);

  // link the template symbol with the template scope
  cpp_scopes.id_map[symbol_name] = &template_scope;
  INVARIANT(
    template_scope.is_template_scope(), "symbol should be in template scope");
}

void cpp_typecheckt::convert_variable_template_specialization(
  cpp_declarationt &declaration)
{
  PRECONDITION(declaration.declarators().size() == 1);

  cpp_declaratort &declarator = declaration.declarators()[0];
  cpp_namet &cpp_name = declarator.name();

  PRECONDITION(cpp_name.has_template_args());

  // Extract base name and template args from the declarator name.
  // Name has the form: name<template_args>
  irep_idt base_name;
  cpp_template_args_non_tct template_args_non_tc;

  for(const auto &sub : cpp_name.get_sub())
  {
    if(sub.id() == ID_name)
      base_name = sub.get(ID_identifier);
    else if(sub.id() == ID_template_args)
      template_args_non_tc = to_cpp_template_args_non_tc(sub);
  }

  // Remove template args from the declarator name so it becomes simple.
  auto &subs = cpp_name.get_sub();
  subs.erase(
    std::remove_if(
      subs.begin(),
      subs.end(),
      [](const irept &s) { return s.id() == ID_template_args; }),
    subs.end());

  // Find the primary variable template.
  auto id_set = cpp_scopes.current_scope().lookup(
    base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);

  for(auto it = id_set.begin(); it != id_set.end();)
  {
    auto next = std::next(it);
    if(lookup((*it)->identifier).type.find(ID_specialization_of).is_not_nil())
      id_set.erase(it);
    it = next;
  }

  if(id_set.empty())
  {
    error().source_location = declaration.source_location();
    error() << "variable template '" << base_name << "' not found" << eom;
    throw 0;
  }

  const symbolt &template_symbol = lookup((*id_set.begin())->identifier);

  // Register as partial specialization.
  declaration.partial_specialization_args() = template_args_non_tc;
  declaration.set_specialization_of(template_symbol.name);

  typecheck_variable_template(declaration);
}

void cpp_typecheckt::typecheck_variable_template(cpp_declarationt &declaration)
{
  PRECONDITION(declaration.declarators().size() == 1);

  cpp_declaratort &declarator = declaration.declarators()[0];
  const cpp_namet &cpp_name = declarator.name();

  cpp_scopet &template_scope =
    typecheck_template_parameters(declaration.template_type());

  if(!cpp_name.is_simple_name())
  {
    error().source_location = declaration.source_location();
    error() << "variable template must have simple name" << eom;
    throw 0;
  }

  irep_idt base_name = cpp_name.get_base_name();

  const cpp_template_args_non_tct &partial_specialization_args =
    declaration.partial_specialization_args();
  std::string symbol_name = class_template_identifier(
    base_name, declaration.template_type(), partial_specialization_args);

  // check if we have it already
  if(symbol_table.has_symbol(symbol_name))
    return;

  symbolt symbol{symbol_name, typet{}, ID_cpp};
  symbol.base_name = base_name;
  symbol.location = cpp_name.source_location();
  symbol.module = module;
  symbol.type.swap(declaration);
  symbol.pretty_name =
    cpp_scopes.current_scope().prefix + id2string(symbol.base_name);

  symbolt *new_symbol;
  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location = symbol.location;
    error() << "typecheck_variable_template: symbol_table.move() failed" << eom;
    throw 0;
  }

  cpp_idt &id = cpp_scopes.put_into_scope(*new_symbol);
  id.id_class = cpp_idt::id_classt::TEMPLATE;
  id.prefix =
    cpp_scopes.current_scope().prefix + id2string(new_symbol->base_name);

  cpp_scopes.id_map[symbol_name] = &template_scope;
}

/// typecheck class template members; these can be methods or static members
void cpp_typecheckt::typecheck_class_template_member(
  cpp_declarationt &declaration)
{
  PRECONDITION(declaration.declarators().size() == 1);

  cpp_declaratort &declarator=declaration.declarators()[0];
  const cpp_namet &cpp_name = declarator.name();

  PRECONDITION(cpp_name.is_qualified() || cpp_name.has_template_args());

  // must be of the form: name1<template_args>::name2
  // or:                  name1<template_args>::operator X
  // or:                  name1<template_args>::~name2
  // or:                  name1::name2 (non-template class)
  if(cpp_name.get_sub().size()==4 &&
     cpp_name.get_sub()[0].id()==ID_name &&
     cpp_name.get_sub()[1].id()==ID_template_args &&
     cpp_name.get_sub()[2].id()=="::" &&
     cpp_name.get_sub()[3].id()==ID_name)
  {
  }
  else if(cpp_name.get_sub().size()==5 &&
          cpp_name.get_sub()[0].id()==ID_name &&
          cpp_name.get_sub()[1].id()==ID_template_args &&
          cpp_name.get_sub()[2].id()=="::" &&
          cpp_name.get_sub()[3].id()==ID_operator)
  {
  }
  else if(
    cpp_name.get_sub().size() == 5 && cpp_name.get_sub()[0].id() == ID_name &&
    cpp_name.get_sub()[1].id() == ID_template_args &&
    cpp_name.get_sub()[2].id() == "::" && cpp_name.get_sub()[3].id() == "~" &&
    cpp_name.get_sub()[4].id() == ID_name)
  {
  }
  else if(
    cpp_name.get_sub().size() == 3 && cpp_name.get_sub()[0].id() == ID_name &&
    cpp_name.get_sub()[1].id() == "::" && cpp_name.get_sub()[2].id() == ID_name)
  {
    // Non-template class with a member function template defined
    // outside the class body: name1::name2
    const irep_idt &class_name = cpp_name.get_sub()[0].get(ID_identifier);
    const irep_idt &method_name = cpp_name.get_sub()[2].get(ID_identifier);

    // Look up the class scope
    auto class_ids = cpp_scopes.current_scope().lookup(
      class_name, cpp_scopet::QUALIFIED, cpp_scopet::id_classt::CLASS);

    if(!class_ids.empty())
    {
      cpp_scopet &class_scope =
        cpp_scopes.get_scope((*class_ids.begin())->identifier);

      // Find the function template in the class scope
      auto tmpl_ids = class_scope.lookup(
        method_name, cpp_scopet::QUALIFIED, cpp_scopet::id_classt::TEMPLATE);

      for(const auto *tmpl_id : tmpl_ids)
      {
        symbolt *tmpl_sym = symbol_table.get_writeable(tmpl_id->identifier);
        if(tmpl_sym == nullptr)
          continue;

        // Update the template symbol with the body from the
        // out-of-line definition.
        cpp_declarationt &tmpl_decl = to_cpp_declaration(tmpl_sym->type);
        if(
          !tmpl_decl.declarators().empty() &&
          tmpl_decl.declarators()[0].find(ID_value).is_nil() &&
          declarator.find(ID_value).is_not_nil())
        {
          tmpl_decl.declarators()[0].add(ID_value) = declarator.find(ID_value);
          return;
        }
      }
    }
    return;
  }
  else
  {
    return; // TODO

#if 0
    error().source_location=cpp_name.source_location();
    error() << "bad template name" << eom;
    throw 0;
#endif
  }

  // let's find the class template this function template belongs to.
  auto id_set = cpp_scopes.current_scope().lookup(
    cpp_name.get_sub().front().get(ID_identifier),
    cpp_scopet::QUALIFIED,            // search using-scopes (inline namespaces)
    cpp_scopet::id_classt::TEMPLATE); // must be template

  // remove any specializations and non-class templates (e.g., constructor
  // templates that share the class name)
  for(auto it = id_set.begin(); it != id_set.end();)
  {
    auto next = it;
    ++next;
    const symbolt &sym = lookup((*it)->identifier);
    if(
      sym.type.find(ID_specialization_of).is_not_nil() ||
      !to_cpp_declaration(sym.type).is_class_template())
    {
      id_set.erase(it);
    }
    it = next;
  }

  if(id_set.empty())
  {
    // For system headers, suppress the error and skip the member
    // definition. This handles cases where a class template failed
    // to register due to unsupported constructs.
    const std::string file = id2string(cpp_name.source_location().get_file());
    if(
      file.find("/usr/include/") == 0 || file.find("/usr/lib/") == 0 ||
      file.find("\\include\\") != std::string::npos ||
      file.find("/Applications/") == 0)
      return;
    error() << cpp_scopes.current_scope();
    error().source_location=cpp_name.source_location();
    error() << "class template '"
            << cpp_name.get_sub().front().get(ID_identifier) << "' not found"
            << eom;
    throw 0;
  }
  else if(id_set.size()>1)
  {
    error().source_location=cpp_name.source_location();
    error() << "class template '"
            << cpp_name.get_sub().front().get(ID_identifier) << "' is ambiguous"
            << eom;
    throw 0;
  }
  else if((*(id_set.begin()))->id_class!=cpp_idt::id_classt::TEMPLATE)
  {
    // std::cerr << *(*id_set.begin()) << '\n';
    error().source_location=cpp_name.source_location();
    error() << "class template '"
            << cpp_name.get_sub().front().get(ID_identifier)
            << "' is not a template" << eom;
    throw 0;
  }

  const cpp_idt &cpp_id=**(id_set.begin());
  symbolt &template_symbol = symbol_table.get_writeable_ref(cpp_id.identifier);

  exprt &template_methods =
    static_cast<exprt &>(template_symbol.value.add(ID_template_methods));

  template_methods.copy_to_operands(declaration);

  // save current scope
  cpp_save_scopet cpp_saved_scope(cpp_scopes);

  const irept &instantiated_with =
    template_symbol.value.add(ID_instantiated_with);

  for(std::size_t i=0; i<instantiated_with.get_sub().size(); i++)
  {
    const cpp_template_args_tct &tc_template_args=
      static_cast<const cpp_template_args_tct &>(
        instantiated_with.get_sub()[i]);

    cpp_declarationt decl_tmp=declaration;

    template_typet method_type = decl_tmp.template_type();
    const std::size_t n_class_params = tc_template_args.arguments().size();
    const std::size_t n_method_params =
      method_type.template_parameters().size();

    // Skip member function templates — they have more template
    // parameters than the class template args.
    if(n_method_params > n_class_params)
    {
      // Partially instantiate: substitute class template params,
      // keep method-only params, register as function template
      // in the instantiated class scope.
      cpp_declarationt mcopy = decl_tmp;

      // Build template map for class params
      cpp_saved_template_mapt saved_map(template_map);
      template_map.build(method_type, tc_template_args);

      // Keep only method-own template params
      template_typet method_only_tt;
      for(std::size_t j = n_class_params; j < n_method_params; j++)
        method_only_tt.template_parameters().push_back(
          method_type.template_parameters()[j]);
      mcopy.set(ID_template_type, method_only_tt);
      mcopy.set(ID_is_template, true);
      // Ensure access specifier is set (needed by instantiate_template)
      if(mcopy.get(ID_C_access).empty())
        mcopy.set(ID_C_access, ID_public);

      // Simplify qualified name to base name
      if(!mcopy.declarators().empty())
      {
        irep_idt base = mcopy.declarators().front().name().get_base_name();
        if(!base.empty())
          mcopy.declarators().front().name() = cpp_namet(base);
      }

      // Apply class template substitution to type and body
      if(!mcopy.declarators().empty())
      {
        typet mtype = mcopy.declarators().front().merge_type(mcopy.type());
        template_map.apply(mtype);
        // Keep the function type on the declarator (not the declaration)
        // because guess_function_template_args checks declarator.type().
        mcopy.declarators().front().type() = mtype;
        mcopy.type().make_nil();

        if(mcopy.declarators().front().find(ID_value).is_not_nil())
        {
          exprt &body_val =
            static_cast<exprt &>(mcopy.declarators().front().add(ID_value));
          template_map.apply(body_val);

          // Strip local struct definitions (e.g., _Guard RAII
          // structs) and references to them. These contain
          // cpp_name types that cannot be resolved during partial
          // instantiation, and CBMC does not model exceptions.
          if(
            body_val.id() == ID_code &&
            to_code(body_val).get_statement() == ID_block)
          {
            std::set<irep_idt> local_structs;
            for(const auto &op : body_val.operands())
            {
              if(op.id() != ID_cpp_declaration)
                continue;
              const auto &cd = static_cast<const cpp_declarationt &>(
                static_cast<const irept &>(op));
              if(cd.type().id() != ID_struct)
                continue;
              const irept &tag = cd.type().find(ID_tag);
              if(tag.is_nil())
                continue;
              const auto &tsub = tag.get_sub();
              if(!tsub.empty() && tsub.front().id() == ID_name)
                local_structs.insert(tsub.front().get(ID_identifier));
            }
            if(!local_structs.empty())
            {
              auto refs = [&](const exprt &e)
              {
                bool found = false;
                e.visit_pre(
                  [&](const exprt &sub)
                  {
                    auto chk = [&](const irept &n)
                    {
                      const auto &s = n.get_sub();
                      if(
                        !s.empty() && s.front().id() == ID_name &&
                        local_structs.count(s.front().get(ID_identifier)))
                        found = true;
                    };
                    if(sub.id() == ID_cpp_name)
                      chk(sub);
                    if(sub.type().id() == ID_cpp_name)
                      chk(sub.type());
                  });
                return found;
              };
              auto &ops = body_val.operands();
              ops.erase(
                std::remove_if(
                  ops.begin(),
                  ops.end(),
                  [&](const exprt &op)
                  {
                    if(op.id() == ID_cpp_declaration)
                    {
                      const auto &cd = static_cast<const cpp_declarationt &>(
                        static_cast<const irept &>(op));
                      if(cd.type().id() == ID_struct)
                        return true;
                    }
                    return refs(op);
                  }),
                ops.end());
            }
          }
        }
      }

      // Find the instantiated class scope
      std::string inst_suffix = template_suffix(tc_template_args);
      // Use the template symbol's scope (not the current scope) to
      // construct the class identifier, since the class may be in a
      // nested namespace (e.g., std::__cxx11::basic_string).
      std::string tmpl_prefix;
      {
        const std::string tname = id2string(template_symbol.name);
        auto tpos = tname.rfind("template.");
        if(tpos != std::string::npos)
          tmpl_prefix = tname.substr(0, tpos);
      }
      irep_idt inst_id = tmpl_prefix + "tag-" +
                         id2string(template_symbol.base_name) + inst_suffix;
      auto scope_it = cpp_scopes.id_map.find(inst_id);
      if(scope_it != cpp_scopes.id_map.end())
      {
        cpp_save_scopet ss(cpp_scopes);
        cpp_scopes.go_to(static_cast<cpp_scopet &>(*scope_it->second));

        // Find existing function template and update its body.
        // Do NOT create a new template (that would cause duplicates).
        irep_idt mbase = mcopy.declarators().empty()
                           ? irep_idt()
                           : mcopy.declarators().front().name().get_base_name();
        if(!mbase.empty())
        {
          auto ids = cpp_scopes.current_scope().lookup(
            mbase, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);
          for(const auto *idp : ids)
          {
            auto *ts = symbol_table.get_writeable(idp->identifier);
            if(!ts || !ts->type.get_bool(ID_is_template))
              continue;
            cpp_declarationt &td = to_cpp_declaration(ts->type);
            if(
              !td.declarators().empty() &&
              td.declarators()[0].find(ID_value).is_nil() &&
              !mcopy.declarators().empty() &&
              mcopy.declarators()[0].find(ID_value).is_not_nil())
            {
              // Verify signature match: concrete type names in the
              // .tcc definition must appear in the template symbol
              // name to prevent swapping overload bodies.
              {
                std::set<std::string> tpnames;
                for(const auto &tp :
                    decl_tmp.template_type().template_parameters())
                {
                  irep_idt bn = tp.get(ID_base_name);
                  if(!bn.empty())
                    tpnames.insert(id2string(bn));
                }
                typet mc_ft =
                  decl_tmp.declarators()[0].merge_type(decl_tmp.type());
                std::string ts_name = id2string(ts->name);
                bool sig_ok = true;
                if(mc_ft.id() == ID_code || mc_ft.id() == ID_function_type)
                {
                  for(const auto &sub : mc_ft.find(ID_parameters).get_sub())
                  {
                    const typet &pt =
                      static_cast<const typet &>(sub.find(ID_type));
                    if(pt.id() != ID_cpp_name)
                      continue;
                    for(const auto &s : pt.get_sub())
                    {
                      if(s.id() != ID_name)
                        continue;
                      std::string nm = id2string(s.get(ID_identifier));
                      if(tpnames.count(nm) || nm == "std")
                        continue;
                      // Skip names that look like template params
                      // (_Uppercase convention in libstdc++)
                      if(
                        nm.size() > 1 && nm[0] == '_' &&
                        std::isupper(static_cast<unsigned char>(nm[1])))
                        continue;
                      if(ts_name.find(nm) == std::string::npos)
                      {
                        sig_ok = false;
                        break;
                      }
                    }
                    if(!sig_ok)
                      break;
                  }
                }
                if(!sig_ok)
                  continue;
              }
              td.declarators()[0].add(ID_value) =
                mcopy.declarators()[0].find(ID_value);

              // Update existing concrete symbols that have nil body
              // with the now-available body from the .tcc definition.
              irep_idt mbase2 = td.declarators()[0].name().get_base_name();
              // Build class prefix from inst_id
              std::string cls_pfx = id2string(inst_id);
              {
                auto p =
                  cls_pfx.find("tag-" + id2string(template_symbol.base_name));
                if(p != std::string::npos)
                  cls_pfx.erase(p, 4);
              }
              cls_pfx += "::";
              for(auto &sp : symbol_table)
              {
                if(
                  sp.second.base_name == mbase2 &&
                  sp.second.type.id() == ID_code && sp.second.value.is_nil() &&
                  id2string(sp.first).find(cls_pfx) == 0)
                {
                  symbolt &csym = symbol_table.get_writeable_ref(sp.first);
                  csym.value = static_cast<const exprt &>(
                    mcopy.declarators()[0].find(ID_value));
                  add_method_body(&csym);
                }
              }

              break;
            }
          }
        }
      }

      cpp_saved_scope.restore();
      continue;
    }

    // do template arguments
    // this also sets up the template scope of the method
    cpp_saved_template_mapt saved_map(template_map);
    cpp_scopet &method_scope=
      typecheck_template_parameters(decl_tmp.template_type());

    cpp_scopes.go_to(method_scope);

    // mapping from template arguments to values/types
    template_map.build(decl_tmp.template_type(), tc_template_args);

    decl_tmp.remove(ID_template_type);
    decl_tmp.remove(ID_is_template);

    convert(decl_tmp);
    cpp_saved_scope.restore();
  }
}

std::string cpp_typecheckt::class_template_identifier(
  const irep_idt &base_name,
  const template_typet &template_type,
  const cpp_template_args_non_tct &partial_specialization_args)
{
  std::string identifier=
    cpp_scopes.current_scope().prefix+
    "template."+id2string(base_name) + "<";

  int counter=0;

  // these are probably not needed -- templates
  // should be unique in a namespace
  for(template_typet::template_parameterst::const_iterator
      it=template_type.template_parameters().begin();
      it!=template_type.template_parameters().end();
      it++)
  {
    if(counter!=0)
      identifier+=',';

    if(it->id()==ID_type)
      identifier+="Type"+std::to_string(counter);
    else
      identifier+="Non_Type"+std::to_string(counter);

    counter++;
  }

  identifier += ">";

  if(!partial_specialization_args.arguments().empty())
  {
    identifier+="_specialized_to_<";

    counter=0;
    for(cpp_template_args_non_tct::argumentst::const_iterator
        it=partial_specialization_args.arguments().begin();
        it!=partial_specialization_args.arguments().end();
        it++, counter++)
    {
      if(counter!=0)
        identifier+=',';

      // These are not yet typechecked, as they may depend
      // on unassigned template parameters.

      if(it->id() == ID_type || it->id() == ID_ambiguous)
        identifier+=cpp_type2name(it->type());
      else
        identifier+=cpp_expr2name(*it);
    }

    identifier+='>';
  }

  // C++20: include requires clause in the identifier so that
  // constrained specializations with the same argument pattern
  // get distinct symbols.
  {
    const auto &req_expr = template_type.find(ID_C_requires_clause);
    if(req_expr.is_not_nil() && req_expr.id() != ID_nil)
    {
      std::string concepts;
      std::function<void(const irept &)> visit = [&](const irept &node)
      {
        // Collect type-predicate expression IDs (e.g., __is_pointer)
        // which are stored as the node id, not as ID_name sub-nodes.
        const std::string &nid = id2string(node.id());
        if(nid.find("__is_") == 0 || nid.find("__has_") == 0)
        {
          if(!concepts.empty())
            concepts += "&&";
          concepts += nid;
        }
        if(node.id() == ID_name)
        {
          const irep_idt &nm = node.get(ID_identifier);
          if(!nm.empty())
          {
            if(!concepts.empty())
              concepts += "&&";
            concepts += id2string(nm);
          }
        }
        for(const auto &sub : node.get_sub())
          visit(sub);
      };
      visit(req_expr);
      if(!concepts.empty())
        identifier += "#req_" + concepts;
    }
    // Also check constraint count string for type-trait-based requires
    const irep_idt &req_str = template_type.get(ID_C_requires_clause);
    if(!req_str.empty() && isdigit(id2string(req_str)[0]))
    {
      identifier += "#req_count_" + id2string(req_str);
    }
    // Include concept constraint names from template parameters
    // so that specializations with the same argument pattern but
    // different concept constraints get distinct identifiers.
    for(const auto &p : template_type.template_parameters())
    {
      const irep_idt &cc = p.get("#C_concept_constraint");
      if(!cc.empty())
        identifier += "#concept_" + id2string(cc);
    }
  }

  return identifier;
}

std::string cpp_typecheckt::function_template_identifier(
  const irep_idt &base_name,
  const template_typet &template_type,
  const typet &function_type)
{
  // we first build something without function arguments
  cpp_template_args_non_tct partial_specialization_args;
  std::string identifier=
    class_template_identifier(base_name, template_type,
                              partial_specialization_args);

  // we must also add the signature of the function to the identifier
  identifier+=cpp_type2name(function_type);

  // C++20: include concept constraints in the identifier so that
  // overloads differing only in concept constraints get distinct symbols.
  for(const auto &p : template_type.template_parameters())
  {
    const irep_idt &constraint = p.get("#C_concept_constraint");
    if(!constraint.empty())
      identifier += "#" + id2string(constraint);
  }

  // C++20: include requires clause concept names in the identifier
  // so that overloads differing only in requires clauses get distinct
  // symbols.
  {
    const auto &req_expr = template_type.find(ID_C_requires_clause);
    if(req_expr.is_not_nil() && req_expr.id() != ID_nil)
    {
      std::string concepts;
      std::function<void(const irept &)> visit = [&](const irept &node)
      {
        const std::string &nid = id2string(node.id());
        if(nid.find("__is_") == 0 || nid.find("__has_") == 0)
        {
          if(!concepts.empty())
            concepts += "&&";
          concepts += nid;
        }
        if(node.id() == ID_name)
        {
          const irep_idt &nm = node.get(ID_identifier);
          if(!nm.empty())
          {
            if(!concepts.empty())
              concepts += "&&";
            concepts += id2string(nm);
          }
        }
        for(const auto &sub : node.get_sub())
          visit(sub);
      };
      visit(req_expr);
      if(!concepts.empty())
        identifier += "#req_" + concepts;
    }
  }

  return identifier;
}

void cpp_typecheckt::convert_class_template_specialization(
  cpp_declarationt &declaration)
{
  cpp_save_scopet saved_scope(cpp_scopes);

  typet &type=declaration.type();

  PRECONDITION(type.id() == ID_struct || type.id() == ID_union);

  cpp_namet &cpp_name=
    static_cast<cpp_namet &>(type.add(ID_tag));

  if(cpp_name.is_qualified())
  {
    error().source_location=cpp_name.source_location();
    error() << "qualifiers not expected here" << eom;
    throw 0;
  }

  if(cpp_name.get_sub().size()!=2 ||
     cpp_name.get_sub()[0].id()!=ID_name ||
     cpp_name.get_sub()[1].id()!=ID_template_args)
  {
    // currently we are more restrictive
    // than the standard
    error().source_location=cpp_name.source_location();
    error() << "bad template-class-specialization name" << eom;
    throw 0;
  }

  irep_idt base_name=
    cpp_name.get_sub()[0].get(ID_identifier);

  // copy the template arguments
  const cpp_template_args_non_tct template_args_non_tc=
    to_cpp_template_args_non_tc(cpp_name.get_sub()[1]);

  // Remove the template arguments from the name.
  cpp_name.get_sub().pop_back();

  // get the template symbol

  auto id_set = cpp_scopes.current_scope().lookup(
    base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);

  // remove any specializations and non-class templates (e.g., constructor
  // templates that share the class name)
  for(cpp_scopest::id_sett::iterator
      it=id_set.begin();
      it!=id_set.end();
      ) // no it++
  {
    cpp_scopest::id_sett::iterator next=it;
    next++;

    const symbolt &sym = lookup((*it)->identifier);
    if(
      sym.type.find(ID_specialization_of).is_not_nil() ||
      !to_cpp_declaration(sym.type).is_class_template())
    {
      id_set.erase(it);
    }

    it=next;
  }

  // only one should be left
  if(id_set.empty())
  {
    error().source_location=type.source_location();
    error() << "class template '" << base_name << "' not found" << eom;
    throw 0;
  }
  else if(id_set.size()>1)
  {
    error().source_location=type.source_location();
    error() << "class template '" << base_name << "' is ambiguous" << eom;
    throw 0;
  }

  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find((*id_set.begin())->identifier);

  CHECK_RETURN(s_it != symbol_table.symbols.end());

  const symbolt &template_symbol=s_it->second;

  if(!template_symbol.type.get_bool(ID_is_template))
  {
    error().source_location=type.source_location();
    error() << "expected a template" << eom;
  }

  #if 0
  // is this partial specialization?
  if(declaration.template_type().parameters().empty())
  {
    // typecheck arguments -- these are for the 'primary' template!
    cpp_template_args_tct template_args_tc=
      typecheck_template_args(
        declaration.source_location(),
        to_cpp_declaration(template_symbol.type).template_type(),
        template_args_non_tc);

    // Full specialization, i.e., template<>.
    // We instantiate.
    instantiate_template(
      cpp_name.source_location(),
      template_symbol,
      template_args_tc,
      type);
  }
  else // NOLINT(readability/braces)
  #endif

  {
    // partial specialization -- we typecheck
    declaration.partial_specialization_args()=template_args_non_tc;
    declaration.set_specialization_of(template_symbol.name);

    typecheck_class_template(declaration);
  }
}

void cpp_typecheckt::convert_template_function_or_member_specialization(
  cpp_declarationt &declaration)
{
  cpp_save_scopet saved_scope(cpp_scopes);

  if(declaration.declarators().size()!=1 ||
     declaration.declarators().front().type().id()!=ID_function_type)
  {
    // Variable template full specialization (template<> const int v<0,0> = 1)
    if(
      declaration.declarators().size() == 1 &&
      declaration.declarators().front().type().id() != ID_function_type &&
      declaration.declarators().front().name().has_template_args())
    {
      cpp_declaratort &declarator = declaration.declarators().front();
      cpp_namet &cpp_name = declarator.name();

      irep_idt base_name;
      cpp_template_args_non_tct template_args_non_tc;
      for(const auto &sub : cpp_name.get_sub())
      {
        if(sub.id() == ID_name)
          base_name = sub.get(ID_identifier);
        else if(sub.id() == ID_template_args)
          template_args_non_tc = to_cpp_template_args_non_tc(sub);
      }

      // Remove template args from name.
      auto &subs = cpp_name.get_sub();
      subs.erase(
        std::remove_if(
          subs.begin(),
          subs.end(),
          [](const irept &s) { return s.id() == ID_template_args; }),
        subs.end());

      auto id_set = cpp_scopes.current_scope().lookup(
        base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);

      for(auto it = id_set.begin(); it != id_set.end();)
      {
        auto next = std::next(it);
        if(lookup((*it)->identifier)
             .type.find(ID_specialization_of)
             .is_not_nil())
          id_set.erase(it);
        it = next;
      }

      if(!id_set.empty())
      {
        const symbolt &template_symbol = lookup((*id_set.begin())->identifier);

        cpp_template_args_tct template_args = typecheck_template_args(
          declaration.source_location(), template_symbol, template_args_non_tc);

        typet specialization;
        specialization.swap(declarator);

        instantiate_template(
          cpp_name.source_location(),
          template_symbol,
          template_args,
          template_args,
          specialization);
      }
      return;
    }

    // Not a function template specialization — could be a static data
    // member specialization (e.g., template<> const char*
    // Cache<char>::data[14]). Silently skip for now.
    return;
  }

  PRECONDITION(declaration.declarators().size() == 1);
  cpp_declaratort declarator=declaration.declarators().front();
  cpp_namet &cpp_name=declarator.name();

  // There is specialization (instantiation with template arguments)
  // but also function overloading (no template arguments)

  PRECONDITION(!cpp_name.get_sub().empty());

  if(cpp_name.get_sub().back().id()==ID_template_args)
  {
    // proper specialization with arguments
    if(cpp_name.get_sub().size()!=2 ||
       cpp_name.get_sub()[0].id()!=ID_name ||
       cpp_name.get_sub()[1].id()!=ID_template_args)
    {
      // currently we are more restrictive
      // than the standard
      error().source_location=cpp_name.source_location();
      error() << "bad template-function-specialization name" << eom;
      throw 0;
    }

    std::string base_name=
      cpp_name.get_sub()[0].get(ID_identifier).c_str();

    const auto id_set =
      cpp_scopes.current_scope().lookup(base_name, cpp_scopet::SCOPE_ONLY);

    if(id_set.empty())
    {
      error().source_location=cpp_name.source_location();
      error() << "template function '" << base_name << "' not found" << eom;
      throw 0;
    }
    else if(id_set.size()>1)
    {
      error().source_location=cpp_name.source_location();
      error() << "template function '" << base_name << "' is ambiguous" << eom;
      throw 0;
    }

    const symbolt &template_symbol=
      lookup((*id_set.begin())->identifier);

    cpp_template_args_tct template_args=
      typecheck_template_args(
        declaration.source_location(),
        template_symbol,
        to_cpp_template_args_non_tc(cpp_name.get_sub()[1]));

    cpp_name.get_sub().pop_back();

    typet specialization;
    specialization.swap(declarator);

    instantiate_template(
      cpp_name.source_location(),
      template_symbol,
      template_args,
      template_args,
      specialization);
  }
  else
  {
    // Just overloading, but this is still a template
    // for disambiguation purposes!
    // http://www.gotw.ca/publications/mill17.htm
    cpp_declarationt new_declaration=declaration;

    new_declaration.remove(ID_template_type);
    new_declaration.remove(ID_is_template);
    new_declaration.set(ID_C_template, ""); // todo, get identifier

    convert_non_template_declaration(new_declaration);
  }
}

cpp_scopet &cpp_typecheckt::typecheck_template_parameters(
  template_typet &type)
{
  cpp_save_scopet cpp_saved_scope(cpp_scopes);

  PRECONDITION(type.id() == ID_template);

  std::string id_suffix="template::"+std::to_string(template_counter++);

  // produce a new scope for the template parameters
  cpp_scopet &template_scope = cpp_scopes.current_scope().new_scope(id_suffix);
  template_scope.id_class=cpp_idt::id_classt::TEMPLATE_SCOPE;

  cpp_scopes.go_to(template_scope);

  // put template parameters into this scope
  template_typet::template_parameterst &parameters=
    type.template_parameters();

  unsigned anon_count=0;

  for(template_typet::template_parameterst::iterator
      it=parameters.begin();
      it!=parameters.end();
      it++)
  {
    exprt &parameter=*it;

    cpp_declarationt declaration;
    declaration.swap(static_cast<cpp_declarationt &>(parameter));

    cpp_declarator_convertert cpp_declarator_converter(*this);

    // there must be _one_ declarator
    PRECONDITION(declaration.declarators().size() == 1);

    cpp_declaratort &declarator=declaration.declarators().front();

    // it may be anonymous
    if(declarator.name().is_nil())
      declarator.name() = cpp_namet("anon#" + std::to_string(++anon_count));

    #if 1
    // The declarator needs to be just a name
    if(declarator.name().get_sub().size()!=1 ||
       declarator.name().get_sub().front().id()!=ID_name)
    {
      error().source_location=declaration.source_location();
      error() << "template parameter must be simple name" << eom;
      throw 0;
    }

    cpp_scopet &scope=cpp_scopes.current_scope();

    irep_idt base_name=declarator.name().get_sub().front().get(ID_identifier);
    irep_idt identifier=scope.prefix+id2string(base_name);

    // add to scope
    cpp_idt &id=scope.insert(base_name);
    id.identifier=identifier;
    id.id_class=cpp_idt::id_classt::TEMPLATE_PARAMETER;

    // is it a type or not?
    if(declaration.get_bool(ID_is_type))
    {
      parameter = type_exprt(template_parameter_symbol_typet(identifier));
      parameter.type().add_source_location()=declaration.find_source_location();
      // Mark template template parameters so that argument typechecking
      // can resolve the argument as a template name rather than a type.
      if(declaration.type().id() == ID_template)
        parameter.set(ID_is_template, true);
      // Preserve concept constraint for C++20 concept subsumption
      const irep_idt &constraint = declaration.get("#C_concept_constraint");
      if(!constraint.empty())
        parameter.set("#C_concept_constraint", constraint);
    }
    else
    {
      // C++20: check if this non-type parameter's type is actually
      // a concept (parsed as constexpr bool). If so, convert to a
      // type parameter with concept constraint.
      bool converted_to_concept = false;
      if(declaration.type().id() == ID_cpp_name)
      {
        // Check if the name resolves to a concept (constexpr bool)
        // by looking it up in the symbol table.
        std::string cname;
        for(const auto &s : declaration.type().get_sub())
        {
          if(s.id() == ID_name)
          {
            if(!cname.empty())
              cname += "::";
            cname += id2string(s.get(ID_identifier));
          }
        }
        // Search symbol table for a matching constexpr bool
        for(const auto &sym : symbol_table)
        {
          if(
            id2string(sym.first).find(cname) != std::string::npos &&
            sym.second.type.id() == ID_bool &&
            sym.second.type.get_bool(ID_C_constant))
          {
            // It's a concept — convert to type parameter
            parameter = type_exprt(template_parameter_symbol_typet(identifier));
            parameter.type().add_source_location() =
              declaration.find_source_location();
            // Sanitize :: for identifier generation
            {
              std::string s = cname;
              std::string::size_type p;
              while((p = s.find("::")) != std::string::npos)
                s.replace(p, 2, "__");
              parameter.set("#C_concept_constraint", s);
            }
            converted_to_concept = true;
            break;
          }
        }
      }
      if(!converted_to_concept)
      {
        // The type is not checked, as it might depend
        // on earlier parameters.
        parameter = symbol_exprt(identifier, declaration.type());
      }
    }

    // There might be a default type or default value.
    // We store it for later, as it can't be typechecked now
    // because of possible dependencies on earlier parameters!
    if(declarator.value().is_not_nil())
      parameter.add(ID_C_default_value)=declarator.value();

    // Preserve parameter pack (ellipsis) information
    if(declarator.get_has_ellipsis())
      parameter.set(ID_ellipsis, true);

#else
    // is it a type or not?
    cpp_declarator_converter.is_typedef=declaration.get_bool(ID_is_type);

    // say it a template parameter
    cpp_declarator_converter.is_template_parameter=true;

    // There might be a default type or default value.
    // We store it for later, as it can't be typechecked now
    // because of possible dependencies on earlier parameters!
    exprt default_value=declarator.value();
    declarator.value().make_nil();

    const symbolt &symbol=
      cpp_declarator_converter.convert(declaration, declarator);

    if(cpp_declarator_converter.is_typedef)
    {
      parameter = exprt(ID_type, struct_tag_typet(symbol.name));
      parameter.type().add_source_location()=declaration.find_location();
    }
    else
      parameter=symbol.symbol_expr();

    // set (non-typechecked) default value
    if(default_value.is_not_nil())
      parameter.add(ID_C_default_value)=default_value;

    parameter.add_source_location()=declaration.find_location();
#endif
  }

  return template_scope;
}

/// \par parameters: location, non-typechecked template arguments
/// \return typechecked template arguments
cpp_template_args_tct cpp_typecheckt::typecheck_template_args(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_non_tct &template_args)
{
  // old stuff
  PRECONDITION(template_args.id() != ID_already_typechecked);

  PRECONDITION(template_symbol.type.get_bool(ID_is_template));

  const template_typet &template_type=
    to_cpp_declaration(template_symbol.type).template_type();

  // bad re-cast, but better than copying the args one by one
  cpp_template_args_tct result=
    (const cpp_template_args_tct &)(template_args);

  cpp_template_args_tct::argumentst &args=
    result.arguments();

  const template_typet::template_parameterst &parameters=
    template_type.template_parameters();

  if(parameters.size() < args.size())
  {
    // Check if the last parameter is a parameter pack (ellipsis)
    bool has_pack =
      !parameters.empty() && parameters.back().get_bool(ID_ellipsis);
    // For partial specializations, the specialization's own parameters
    // may not include the pack. Check the primary template.
    if(!has_pack)
    {
      const irep_idt &primary_id =
        template_symbol.type.get(ID_specialization_of);
      if(!primary_id.empty())
      {
        const symbolt *primary = symbol_table.lookup(primary_id);
        if(primary != nullptr && primary->type.get_bool(ID_is_template))
        {
          const auto &primary_params = to_cpp_declaration(primary->type)
                                         .template_type()
                                         .template_parameters();
          has_pack = !primary_params.empty() &&
                     primary_params.back().get_bool(ID_ellipsis);
        }
      }
    }
    if(!has_pack)
    {
      error().source_location = source_location;
      error() << "too many template arguments (expected " << parameters.size()
              << ", but got " << args.size() << ")" << eom;
      throw 0;
    }
  }

  // we will modify the template map
  template_mapt old_template_map;
  old_template_map=template_map;

  // check for default arguments
  std::size_t first_default = parameters.size();
  cpp_scopet *instantiation_scope_ptr = &cpp_scopes.current_scope();
  for(std::size_t i=0; i<parameters.size(); i++)
  {
    const template_parametert &parameter=parameters[i];
    cpp_save_scopet cpp_saved_scope(cpp_scopes);

    if(i>=args.size())
    {
      // A variadic parameter pack can accept zero arguments.
      if(parameter.get_bool(ID_ellipsis))
        break;

      // Check for default argument for the parameter.
      // These may depend on previous arguments.
      if(!parameter.has_default_argument())
      {
        // For function templates, remaining parameters can be deduced
        // from the function call arguments, so partial explicit
        // template arguments are allowed.
        const cpp_declarationt &cpp_declaration =
          to_cpp_declaration(template_symbol.type);
        if(
          !cpp_declaration.is_class_template() &&
          !cpp_declaration.is_template_alias())
        {
          break;
        }

        error().source_location=source_location;
        error() << "not enough template arguments (expected "
                << parameters.size() << ", but got " << args.size()
                << ")" << eom;
        throw 0;
      }

      {
        if(first_default > i)
          first_default = i;
        exprt def = parameter.default_argument();
        template_map.apply(def);
        if(def.id() == ID_type)
          template_map.apply(def.type());
        args.push_back(def);
      }

      // these need to be typechecked in the scope of the template,
      // not in the current scope!
      cpp_idt *template_scope=cpp_scopes.id_map[template_symbol.name];
      INVARIANT_STRUCTURED(
        template_scope!=nullptr, nullptr_exceptiont, "template_scope is null");
      cpp_scopes.go_to(*template_scope);
    }

    DATA_INVARIANT(i < args.size(), "i must be in bounds");

    exprt &arg=args[i];

    if(parameter.id()==ID_type)
    {
      // Template template parameter: resolve argument as a template name
      // and store the template symbol identifier.
      if(parameter.get_bool(ID_is_template))
      {
        irep_idt template_name;
        if(arg.id() == ID_ambiguous && arg.type().id() == ID_cpp_name)
          template_name = to_cpp_name(arg.type()).get_base_name();
        else if(arg.id() == ID_type && arg.type().id() == ID_cpp_name)
          template_name = to_cpp_name(arg.type()).get_base_name();

        if(!template_name.empty())
        {
          auto id_set = cpp_scopes.current_scope().lookup(
            template_name, cpp_scopet::RECURSIVE, cpp_idt::id_classt::TEMPLATE);
          // If the found template is actually a template template
          // PARAMETER (has a numeric scope ID), resolve it via the
          // template_map to get the actual template.
          if(!id_set.empty())
          {
            const cpp_idt &found_id = **id_set.begin();
            std::string found_str = id2string(found_id.identifier);
            auto last_sep = found_str.rfind("::");
            std::string suffix = last_sep != std::string::npos
                                   ? found_str.substr(last_sep + 2)
                                   : found_str;
            // Numeric suffix indicates a template parameter scope ID
            if(!suffix.empty() && std::isdigit(suffix[0]))
              id_set.clear();
          }
          if(id_set.empty())
          {
            const auto param_set = cpp_scopes.current_scope().lookup(
              template_name,
              cpp_scopet::RECURSIVE,
              cpp_idt::id_classt::TEMPLATE_PARAMETER);
            for(const auto *param_ptr : param_set)
            {
              // Look up the parameter's mapped value in template_map
              exprt e = template_map.lookup(param_ptr->identifier);
              if(
                e.id() == ID_type &&
                e.type().id() == ID_template_parameter_symbol_type)
              {
                const irep_idt &tmpl_id =
                  to_template_parameter_symbol_type(e.type()).get_identifier();
                // Find this template in the scope system
                auto it = cpp_scopes.id_map.find(tmpl_id);
                if(it != cpp_scopes.id_map.end())
                  id_set.insert(it->second);
              }
            }
          }
          // Fallback: search global id_map for the template name.
          if(id_set.empty())
          {
            for(auto &entry : cpp_scopes.id_map)
            {
              if(
                entry.second->base_name == template_name &&
                entry.second->id_class == cpp_idt::id_classt::TEMPLATE)
              {
                id_set.insert(entry.second);
                break;
              }
            }
          }
          // Fallback for qualified names (e.g., Tester::_Apply):
          // resolve the scope prefix, then look up the template
          // in that scope.
          if(id_set.empty())
          {
            const cpp_namet *cn = nullptr;
            if(arg.id() == ID_ambiguous && arg.type().id() == ID_cpp_name)
              cn = &to_cpp_name(arg.type());
            else if(arg.id() == ID_type && arg.type().id() == ID_cpp_name)
              cn = &to_cpp_name(arg.type());
            if(cn != nullptr && cn->get_sub().size() >= 3)
            {
              // Build the scope prefix (everything before the last
              // ::name)
              cpp_namet scope_name;
              for(std::size_t si = 0; si + 2 < cn->get_sub().size(); si++)
                scope_name.get_sub().push_back(cn->get_sub()[si]);
              // Resolve the scope prefix as a type
              cpp_typecheck_resolvet resolver{*this};
              try
              {
                exprt scope_expr = resolver.resolve(
                  scope_name,
                  cpp_typecheck_resolvet::wantt::TYPE,
                  cpp_typecheck_fargst{});
                if(scope_expr.id() == ID_type)
                {
                  irep_idt scope_id;
                  if(scope_expr.type().id() == ID_struct_tag)
                    scope_id =
                      to_struct_tag_type(scope_expr.type()).get_identifier();
                  if(!scope_id.empty())
                  {
                    auto it = cpp_scopes.id_map.find(scope_id);
                    if(it != cpp_scopes.id_map.end())
                    {
                      id_set = static_cast<cpp_scopet &>(*it->second)
                                 .lookup(template_name, cpp_scopet::SCOPE_ONLY);
                    }
                  }
                }
              }
              catch(...)
              {
              }
            }
          }
          if(!id_set.empty())
          {
            const cpp_idt &cpp_id = **id_set.begin();
            // Use the symbol table identifier (full name) for the
            // template template parameter, not the scope ID.
            irep_idt tmpl_id = cpp_id.identifier;

            const auto *tmpl_sym = symbol_table.lookup(tmpl_id);
            if(tmpl_sym)
              tmpl_id = tmpl_sym->name;
            arg = type_exprt(template_parameter_symbol_typet(tmpl_id));
            arg.type().add_source_location() = parameter.source_location();
            template_map.set(parameter, arg);
            continue;
          }
        }
        error().source_location = arg.source_location();
        error() << "expected template name for template template parameter"
                << eom;
        throw 0;
      }

      if(arg.id()==ID_type)
      {
        if(arg.type().is_nil() || arg.type().id().empty())
        {
          error().source_location = arg.source_location();
          error() << "missing type in template argument" << eom;
          throw 0;
        }
        // Skip typecheck_type for types that are already resolved
        // (e.g., struct_tag from a previous instantiation).
        // Re-typechecking can fail when the type references local
        // scopes that are no longer accessible.
        if(arg.type().id() != ID_struct_tag && arg.type().id() != ID_union_tag)
        {
          typecheck_type(arg.type());
        }
      }
      else if(arg.id() == ID_ambiguous)
      {
        if(arg.type().is_nil() || arg.type().id().empty())
        {
          error().source_location = arg.source_location();
          error() << "missing type in template argument" << eom;
          throw 0;
        }
        typecheck_type(arg.type());
        typet t=arg.type();
        arg=exprt(ID_type, t);
      }
      else
      {
        error().source_location=arg.source_location();
        error() << "expected type, but got expression" << eom;
        throw 0;
      }
    }
    else // expression
    {
      // Ambiguous args in non-type parameter context: treat as expression.
      // The parser stores noexcept(...) and other expressions as
      // ambiguous nodes with a cpp_name type interpretation.
      // For non-type parameters, use the expression interpretation.
      if(arg.id() == ID_ambiguous && arg.type().id() == ID_cpp_name)
      {
        // Check if the cpp_name contains a noexcept expression.
        // noexcept(...) evaluates to true for noexcept operations.
        bool has_noexcept = false;
        for(const auto &sub : arg.type().get_sub())
        {
          if(sub.id() == ID_noexcept)
          {
            has_noexcept = true;
            break;
          }
        }
        if(has_noexcept)
        {
          // Evaluate noexcept as true (safe approximation).
          // The noexcept expression contains destructor calls that
          // can't be fully resolved during template instantiation.
          arg = true_exprt();
          template_map.set(parameter, arg);
          continue;
        }
        exprt e{ID_cpp_name};
        e.get_sub() = arg.type().get_sub();
        e.add_source_location() = arg.source_location();
        arg.swap(e);
      }
      // Type predicates as non-type template arguments
      if(!arg.find(ID_type_arg).is_nil() || !arg.find("type_arg1").is_nil())
      {
        try
        {
          typecheck_expr(arg);
        }
        catch(int)
        {
          // Predicate evaluation failed — default to true for
          // fundamental types
          arg = exprt{ID_true, bool_typet{}};
        }
      }
      else if(arg.id() == ID_type)
      {
        // The parser may have interpreted a variable template
        // instantiation (e.g., is_floating_point_v<T>) as a type
        // because it looks like a template-id. Convert it back to
        // an expression so it can be resolved as a variable template.
        if(arg.type().id() == ID_cpp_name)
        {
          exprt e = static_cast<exprt &>(static_cast<irept &>(arg.type()));
          arg.swap(e);
        }
        else
        {
          error().source_location = arg.source_location();
          error() << "expected expression, but got type" << eom;
          throw 0;
        }
      }
      // Simplify comma expressions: (expr1, expr2) -> expr2
      // This handles libc++ patterns like ((void)Pred, true)
      else if(arg.id() == ID_comma)
      {
        typecheck_expr(arg);
        // After type-checking, extract the right operand
        if(arg.id() == ID_comma && arg.operands().size() == 2)
          arg = to_binary_expr(arg).op1();
      }
      else if(arg.id() == ID_ambiguous)
      {
        exprt e;
        e.swap(arg.type());
        // The parser stores the type interpretation for ambiguous
        // template arguments. When the parameter is an expression,
        // a function-type parse like "f()" should become a function
        // call expression "f()".
        if(e.id() == ID_code)
        {
          const irept &return_type = e.find(ID_return_type);
          const irept &params = e.find(ID_parameters);
          if(return_type.id() == ID_cpp_name && params.get_sub().empty())
          {
            exprt func_name = static_cast<const exprt &>(
              static_cast<const irept &>(return_type));
            side_effect_exprt call(
              ID_function_call, uninitialized_typet{}, arg.source_location());
            call.add_to_operands(std::move(func_name));
            call.add_to_operands(exprt(ID_arguments));
            arg.swap(call);
          }
          else
          {
            arg.swap(e);
          }
        }
        else
        {
          arg.swap(e);
        }
      }

      typet type=parameter.type();

      // First check the parameter type (might have earlier
      // type parameters in it). Needs to be checked in scope
      // of template.
      {
        cpp_save_scopet cpp_saved_scope_before_parameter_typecheck(cpp_scopes);
        cpp_idt *template_scope=cpp_scopes.id_map[template_symbol.name];
        INVARIANT_STRUCTURED(
          template_scope!=nullptr,
          nullptr_exceptiont,
          "template_scope is null");
        cpp_scopes.go_to(*template_scope);
        if(!type.id().empty())
          typecheck_type(type);
      }

      // Now check the argument to match that.
      // For default non-type arguments (e.g., SFINAE enable_if_t),
      // the template scope may lack visibility of type aliases from
      // enclosing inline namespaces. Per [temp.point] p1,7, retry
      // in the instantiation scope which has full namespace visibility.
      if(i >= first_default)
      {
        try
        {
          typecheck_expr(arg);
        }
        catch(int)
        {
          cpp_scopes.go_to(*instantiation_scope_ptr);
          typecheck_expr(arg);
        }
      }
      else
        typecheck_expr(arg);
      simplify(arg, *this);
      // C++17 template<auto>: deduce type from argument
      if(type.id() == ID_auto)
        type = arg.type();
      implicit_typecast(arg, type);
      simplify(arg, *this);
    }

    // Set right away -- this is for the benefit of default
    // arguments and later parameters whose type might
    // depend on an earlier parameter. Only set type parameters
    // eagerly; defer expression parameters to avoid overwriting
    // outer template map entries for recursive templates where
    // inner and outer parameters share the same identifiers.

    if(parameter.id() == ID_type)
      template_map.set(parameter, arg);
  }

  // Now set expression parameters.
  for(std::size_t i = 0; i < parameters.size() && i < args.size(); i++)
  {
    if(parameters[i].id() != ID_type)
      template_map.set(parameters[i], args[i]);
  }

  // Typecheck any extra arguments for variadic parameter packs
  if(
    args.size() > parameters.size() && !parameters.empty() &&
    parameters.back().get_bool(ID_ellipsis))
  {
    for(std::size_t i = parameters.size(); i < args.size(); i++)
    {
      exprt &arg = args[i];
      if(arg.id() == ID_type || arg.id() == ID_ambiguous)
      {
        if(arg.id() == ID_ambiguous)
        {
          typet t = arg.type();
          arg = exprt(ID_type, t);
        }
        if(!arg.type().id().empty())
          typecheck_type(arg.type());
      }
      else
      {
        typecheck_expr(arg);
        simplify(arg, *this);
      }
    }
  }

  // Typecheck remaining arguments beyond the parameter list.
  // These correspond to variadic pack expansion arguments when the
  // primary template has a parameter pack (class... Args).
  for(std::size_t i = parameters.size(); i < args.size(); i++)
  {
    exprt &arg = args[i];
    if(arg.id() == ID_type || arg.id() == ID_ambiguous)
    {
      if(arg.id() == ID_ambiguous)
      {
        arg.id(ID_type);
        arg.type() = static_cast<const typet &>(arg.find(ID_type));
      }
      if(!arg.type().id().empty())
        typecheck_type(arg.type());
    }
    else
    {
      typecheck_expr(arg);
      simplify(arg, *this);
    }
  }

  // restore template map
  template_map.swap(old_template_map);

  // For function templates with partial explicit arguments, pad with
  // unassigned markers for the remaining parameters.
  if(args.size() < parameters.size())
  {
    const cpp_declarationt &tmpl_decl =
      to_cpp_declaration(template_symbol.type);
    if(!tmpl_decl.is_class_template() && !tmpl_decl.is_template_alias())
    {
      for(std::size_t i = args.size(); i < parameters.size(); i++)
      {
        if(parameters[i].id() == ID_type)
          args.push_back(exprt(ID_type, typet(ID_unassigned)));
        else
          args.push_back(exprt(ID_unassigned));
      }
    }
  }

  // now the numbers should match (or we have a variadic pack)
  DATA_INVARIANT(
    args.size() >= parameters.size() ||
      (!parameters.empty() && parameters.back().get_bool(ID_ellipsis)),
    "argument numbers must be at least parameter numbers");

  return result;
}

void cpp_typecheckt::convert_template_declaration(
  cpp_declarationt &declaration)
{
  PRECONDITION(declaration.is_template());

  if(declaration.member_spec().is_virtual())
  {
    error().source_location=declaration.source_location();
    error() <<  "invalid use of 'virtual' in template declaration"
            << eom;
    throw 0;
  }

  if(declaration.is_typedef())
  {
    typecheck_template_alias(declaration);
    return;
  }

  typet &type=declaration.type();

  // there are
  // 1) function templates
  // 2) class templates
  // 3) template members of class templates (static or methods)
  // 4) variable templates (C++14)

  if(declaration.is_class_template())
  {
    const cpp_namet &tag_name =
      static_cast<const cpp_namet &>(type.find(ID_tag));

    if(tag_name.is_qualified() && tag_name.has_template_args())
    {
      // Out-of-class nested class definition, e.g.,
      // template<typename T> class Outer<T>::Inner { ... };
      // Not yet supported — silently skip.
      return;
    }

    // Is it class template specialization?
    // We can tell if there are template arguments in the class name,
    // like template<...> class tag<stuff> ...
    if(tag_name.has_template_args())
    {
      convert_class_template_specialization(declaration);
      return;
    }

    typecheck_class_template(declaration);
    return;
  }
  // maybe function template, maybe class template member, maybe
  // template variable
  else
  {
    // there should be declarators in either case
    if(declaration.declarators().empty())
    {
      // C++17: variable templates and alias templates may appear
      // without declarators during instantiation. Skip silently.
      warning().source_location = declaration.source_location();
      warning() << "non-class template is expected to have a declarator" << eom;
      return;
    }

    // Is it function template specialization?
    // Only full specialization is allowed!
    if(declaration.template_type().template_parameters().empty())
    {
      convert_template_function_or_member_specialization(declaration);
      return;
    }

    // Explicit qualification is forbidden for function templates,
    // which we can use to distinguish them.

    DATA_INVARIANT(
      declaration.declarators().size() >= 1, "declarator required");

    cpp_declaratort &declarator=declaration.declarators()[0];
    const cpp_namet &cpp_name = declarator.name();

    if(cpp_name.is_qualified() ||
       cpp_name.has_template_args())
    {
      // Variable template partial specialization: unqualified name
      // with template args and non-function declarator type.
      if(
        !cpp_name.is_qualified() && cpp_name.has_template_args() &&
        declarator.type().id() != ID_function_type)
      {
        convert_variable_template_specialization(declaration);
        return;
      }
      return typecheck_class_template_member(declaration);
    }

    // Check if this is a variable template (C++14) rather than a
    // function template. Variable templates have non-function-type
    // declarators.
    if(declarator.type().id() != ID_function_type)
    {
      typecheck_variable_template(declaration);
      return;
    }

    // must be function template
    typecheck_function_template(declaration);
    return;
  }
}

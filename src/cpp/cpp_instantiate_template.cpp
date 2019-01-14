/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/base_exceptions.h>
#include <util/simplify_expr.h>

#include <util/c_types.h>

#include "cpp_type2name.h"

std::string cpp_typecheckt::template_suffix(
  const cpp_template_args_tct &template_args)
{
  // quick hack
  std::string result="<";
  bool first=true;

  const cpp_template_args_tct::argumentst &arguments=
    template_args.arguments();

  for(const auto &expr : arguments)
  {
    if(first)
      first=false;
    else
      result+=',';

    DATA_INVARIANT(
      expr.id() != ID_ambiguous, "template argument must not be ambiguous");

    if(expr.id()==ID_type)
    {
      const typet &type=expr.type();
      if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
        result += id2string(to_tag_type(type).get_identifier());
      else
        result+=cpp_type2name(type);
    }
    else // expression
    {
      exprt e=expr;
      make_constant(e);

      // this must be a constant, which includes true/false
      mp_integer i;

      if(e.is_true())
        i=1;
      else if(e.is_false())
        i=0;
      else if(to_integer(to_constant_expr(e), i))
      {
        error().source_location = expr.find_source_location();
        error() << "template argument expression expected to be "
                << "scalar constant, but got `"
                << to_string(e) << "'" << eom;
        throw 0;
      }

      result+=integer2string(i);
    }
  }

  result+='>';

  return result;
}

void cpp_typecheckt::show_instantiation_stack(std::ostream &out)
{
  for(const auto &e : instantiation_stack)
  {
    const symbolt &symbol = lookup(e.identifier);
    out << "instantiating `" << symbol.pretty_name << "' with <";

    forall_expr(a_it, e.full_template_args.arguments())
    {
      if(a_it != e.full_template_args.arguments().begin())
        out << ", ";

      if(a_it->id()==ID_type)
        out << to_string(a_it->type());
      else
        out << to_string(*a_it);
    }

    out << "> at " << e.source_location << '\n';
  }
}

const symbolt &cpp_typecheckt::class_template_symbol(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_tct &specialization_template_args,
  const cpp_template_args_tct &full_template_args)
{
  // we should never get 'unassigned' here
  assert(!full_template_args.has_unassigned());

  // do we have args?
  if(full_template_args.arguments().empty())
  {
    error().source_location=source_location;
    error() << "`" << template_symbol.base_name
            << "' is a template; thus, expected template arguments"
            << eom;
    throw 0;
  }

  // produce new symbol name
  std::string suffix=template_suffix(full_template_args);

  cpp_scopet *template_scope=
    static_cast<cpp_scopet *>(cpp_scopes.id_map[template_symbol.name]);

  INVARIANT_STRUCTURED(
    template_scope!=nullptr, nullptr_exceptiont, "template_scope is null");

  irep_idt identifier=
    id2string(template_scope->prefix)+
    "tag-"+id2string(template_symbol.base_name)+
    id2string(suffix);

  // already there?
  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(identifier);
  if(s_it!=symbol_table.symbols.end())
    return s_it->second;

  // Create as incomplete struct, but mark as
  // "template_class_instance", to be elaborated later.
  symbolt new_symbol;
  new_symbol.name=identifier;
  new_symbol.pretty_name=template_symbol.pretty_name;
  new_symbol.location=template_symbol.location;
  new_symbol.type = struct_typet();
  to_struct_type(new_symbol.type).make_incomplete();
  new_symbol.type.set(ID_tag, template_symbol.type.find(ID_tag));
  if(template_symbol.type.get_bool(ID_C_class))
    new_symbol.type.set(ID_C_class, true);
  new_symbol.type.set(ID_template_class_instance, true);
  new_symbol.type.add_source_location()=template_symbol.location;
  new_symbol.type.set(
    ID_specialization_template_args, specialization_template_args);
  new_symbol.type.set(ID_full_template_args, full_template_args);
  new_symbol.type.set(ID_identifier, template_symbol.name);
  new_symbol.mode=template_symbol.mode;
  new_symbol.base_name=template_symbol.base_name;
  new_symbol.is_type=true;

  symbolt *s_ptr;
  symbol_table.move(new_symbol, s_ptr);

  // put into template scope
  cpp_idt &id=cpp_scopes.put_into_scope(*s_ptr, *template_scope);

  id.id_class=cpp_idt::id_classt::CLASS;
  id.is_scope=true;
  id.prefix=template_scope->prefix+
            id2string(s_ptr->base_name)+
            id2string(suffix)+"::";
  id.class_identifier=s_ptr->name;
  id.id_class=cpp_idt::id_classt::CLASS;

  return *s_ptr;
}

/// elaborate class template instances
void cpp_typecheckt::elaborate_class_template(
  const typet &type)
{
  if(type.id() != ID_struct_tag)
    return;

  const symbolt &symbol = lookup(to_struct_tag_type(type));

  // Make a copy, as instantiate will destroy the symbol type!
  const typet t_type=symbol.type;

  if(t_type.id() == ID_struct && t_type.get_bool(ID_template_class_instance))
  {
    instantiate_template(
      type.source_location(),
      lookup(t_type.get(ID_identifier)),
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_specialization_template_args)),
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_full_template_args)));
  }
}

/// \par parameters: location of the instantiation,
/// the identifier of the template symbol,
/// typechecked template arguments,
/// an (optional) specialization
#define MAX_DEPTH 50

const symbolt &cpp_typecheckt::instantiate_template(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_tct &specialization_template_args,
  const cpp_template_args_tct &full_template_args,
  const typet &specialization)
{
#ifdef DEBUG
  std::cout << "instantiate_template: " << template_symbol.name << '\n';
#endif

  if(instantiation_stack.size()==MAX_DEPTH)
  {
    error().source_location=source_location;
    error() << "reached maximum template recursion depth ("
            << MAX_DEPTH << ")" << eom;
    throw 0;
  }

  instantiation_levelt i_level(instantiation_stack);
  instantiation_stack.back().source_location=source_location;
  instantiation_stack.back().identifier=template_symbol.name;
  instantiation_stack.back().full_template_args=full_template_args;

#ifdef DEBUG
  std::cout << "L: " << source_location << '\n';
  std::cout << "I: " << template_symbol.name << '\n';
#endif

  cpp_saved_template_mapt saved_map(template_map);

  bool specialization_given=specialization.is_not_nil();

  // we should never get 'unassigned' here
  assert(!specialization_template_args.has_unassigned());
  assert(!full_template_args.has_unassigned());

#ifdef DEBUG
  std::cout << "A: <";
  forall_expr(it, specialization_template_args.arguments())
  {
    if(it!=specialization_template_args.arguments().begin())
      std::cout << ", ";
    if(it->id()==ID_type)
      std::cout << to_string(it->type());
    else
      std::cout << to_string(*it);
  }
  std::cout << ">\n\n";
#endif

  // do we have arguments?
  if(full_template_args.arguments().empty())
  {
    error().source_location=source_location;
    error() << "`" << template_symbol.base_name
            << "' is a template; thus, expected template arguments"
            << eom;
    throw 0;
  }

  // produce new symbol name
  std::string suffix=template_suffix(full_template_args);

  // we need the template scope to see the template parameters
  cpp_scopet *template_scope=
    static_cast<cpp_scopet *>(cpp_scopes.id_map[template_symbol.name]);

  if(template_scope==nullptr)
  {
    error().source_location=source_location;
    error() << "identifier: " << template_symbol.name << '\n'
            << "template instantiation error: scope not found" << eom;
    throw 0;
  }

  // produce new declaration
  cpp_declarationt new_decl=to_cpp_declaration(template_symbol.type);

  // The new one is not a template any longer, but we remember the
  // template type that was used.
  template_typet template_type=new_decl.template_type();
  new_decl.remove(ID_is_template);
  new_decl.remove(ID_template_type);
  new_decl.set(ID_C_template, template_symbol.name);
  new_decl.set(ID_C_template_arguments, specialization_template_args);

  // save old scope
  cpp_save_scopet saved_scope(cpp_scopes);

  // mapping from template parameters to values/types
  template_map.build(template_type, specialization_template_args);

  // enter the template scope
  cpp_scopes.go_to(*template_scope);

  // Is it a template method?
  // It's in the scope of a class, and not a class itself.
  bool is_template_method=
    cpp_scopes.current_scope().get_parent().is_class() &&
    new_decl.type().id()!=ID_struct;

  irep_idt class_name;

  if(is_template_method)
    class_name=cpp_scopes.current_scope().get_parent().identifier;

  // sub-scope for fixing the prefix
  std::string subscope_name=id2string(template_scope->identifier)+suffix;

  // let's see if we have the instance already
  cpp_scopest::id_mapt::iterator scope_it=
    cpp_scopes.id_map.find(subscope_name);

  if(scope_it!=cpp_scopes.id_map.end())
  {
    cpp_scopet &scope=cpp_scopes.get_scope(subscope_name);

    const auto id_set =
      scope.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

    if(id_set.size()==1)
    {
      // It has already been instantiated!
      const cpp_idt &cpp_id = **id_set.begin();

      assert(cpp_id.id_class == cpp_idt::id_classt::CLASS ||
             cpp_id.id_class == cpp_idt::id_classt::SYMBOL);

      const symbolt &symb=lookup(cpp_id.identifier);

      // continue if the type is incomplete only
      if(cpp_id.id_class==cpp_idt::id_classt::CLASS &&
         symb.type.id()==ID_struct)
        return symb;
      else if(symb.value.is_not_nil())
        return symb;
    }

    cpp_scopes.go_to(scope);
  }
  else
  {
    // set up a scope as subscope of the template scope
    cpp_scopet &sub_scope=
      cpp_scopes.current_scope().new_scope(subscope_name);
    sub_scope.id_class=cpp_idt::id_classt::TEMPLATE_SCOPE;
    sub_scope.prefix=template_scope->get_parent().prefix;
    sub_scope.suffix=suffix;
    sub_scope.add_using_scope(template_scope->get_parent());
    cpp_scopes.go_to(sub_scope);
    cpp_scopes.id_map.insert(
      cpp_scopest::id_mapt::value_type(subscope_name, &sub_scope));
  }

  // store the information that the template has
  // been instantiated using these arguments
  {
    // need non-const handle on template symbol
    symbolt &s=*symbol_table.get_writeable(template_symbol.name);
    irept &instantiated_with = s.value.add(ID_instantiated_with);
    instantiated_with.get_sub().push_back(specialization_template_args);
  }

  #ifdef DEBUG
  std::cout << "CLASS MAP:\n";
  template_map.print(std::cout);
  #endif

  // fix the type
  {
    typet declaration_type=new_decl.type();

    // specialization?
    if(specialization_given)
    {
      if(declaration_type.id()==ID_struct)
      {
        declaration_type=specialization;
        declaration_type.add_source_location()=source_location;
      }
      else
      {
        irept tmp=specialization;
        new_decl.declarators()[0].swap(tmp);
      }
    }

    template_map.apply(declaration_type);
    new_decl.type().swap(declaration_type);
  }

  if(new_decl.type().id()==ID_struct)
  {
    // a class template
    convert_non_template_declaration(new_decl);

    // also instantiate all the template methods
    const exprt &template_methods = static_cast<const exprt &>(
      template_symbol.value.find(ID_template_methods));

    for(auto &tm : template_methods.operands())
    {
      saved_scope.restore();

      cpp_declarationt method_decl=
        static_cast<const cpp_declarationt &>(
          static_cast<const irept &>(tm));

      // copy the type of the template method
      template_typet method_type=
        method_decl.template_type();

      // do template parameters
      // this also sets up the template scope of the method
      cpp_scopet &method_scope=
        typecheck_template_parameters(method_type);

      cpp_scopes.go_to(method_scope);

      // mapping from template arguments to values/types
      template_map.build(method_type, specialization_template_args);
#ifdef DEBUG
      std::cout << "METHOD MAP:\n";
      template_map.print(std::cout);
#endif

      method_decl.remove(ID_template_type);
      method_decl.remove(ID_is_template);

      convert(method_decl);
    }

    const irep_idt& new_symb_id = new_decl.type().get(ID_identifier);
    symbolt &new_symb = symbol_table.get_writeable_ref(new_symb_id);

    // add template arguments to type in order to retrieve template map when
    // typechecking function body
    new_symb.type.set(ID_C_template, template_type);
    new_symb.type.set(ID_C_template_arguments, specialization_template_args);

#ifdef DEBUG
    std::cout << "instance symbol: " << new_symb.name << "\n\n";
    std::cout << "template type: " << template_type.pretty() << "\n\n";
#endif

    return new_symb;
  }

  if(is_template_method)
  {
    symbolt &symb=*symbol_table.get_writeable(class_name);

    assert(new_decl.declarators().size() == 1);

    if(new_decl.member_spec().is_virtual())
    {
      error().source_location=new_decl.source_location();
      error() << "invalid use of `virtual' in template declaration"
              << eom;
      throw 0;
    }

    if(new_decl.is_typedef())
    {
      error().source_location=new_decl.source_location();
      error() << "template declaration for typedef" << eom;
      throw 0;
    }

    if(new_decl.storage_spec().is_extern() ||
       new_decl.storage_spec().is_auto() ||
       new_decl.storage_spec().is_register() ||
       new_decl.storage_spec().is_mutable())
    {
      error().source_location=new_decl.source_location();
      error() << "invalid storage class specified for template field"
              << eom;
      throw 0;
    }

    bool is_static=new_decl.storage_spec().is_static();
    irep_idt access = new_decl.get(ID_C_access);

    assert(!access.empty());
    assert(symb.type.id()==ID_struct);

    typecheck_compound_declarator(
      symb,
      new_decl,
      new_decl.declarators()[0],
      to_struct_type(symb.type).components(),
      access,
      is_static,
      false,
      false);

    return lookup(to_struct_type(symb.type).components().back().get_name());
  }

  // not a class template, not a class template method,
  // it must be a function template!

  assert(new_decl.declarators().size()==1);

  convert_non_template_declaration(new_decl);

  const symbolt &symb=
    lookup(new_decl.declarators()[0].get(ID_identifier));

  return symb;
}

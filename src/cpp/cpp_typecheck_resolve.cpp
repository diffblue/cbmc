/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck_resolve.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <cstdlib>
#include <algorithm>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include <ansi-c/anonymous_member.h>
#include <ansi-c/merged_type.h>

#include "cpp_typecheck.h"
#include "cpp_template_type.h"
#include "cpp_type2name.h"
#include "cpp_util.h"
#include "cpp_convert_type.h"

cpp_typecheck_resolvet::cpp_typecheck_resolvet(cpp_typecheckt &_cpp_typecheck):
  cpp_typecheck(_cpp_typecheck),
  original_scope(nullptr) // set in resolve_scope()
{
}

void cpp_typecheck_resolvet::convert_identifiers(
  const cpp_scopest::id_sett &id_set,
  const cpp_typecheck_fargst &fargs,
  resolve_identifierst &identifiers)
{
  for(const auto &id_ptr : id_set)
  {
    const cpp_idt &identifier = *id_ptr;
    exprt e=convert_identifier(identifier, fargs);

    if(e.is_not_nil())
    {
      if(e.id()==ID_type)
        assert(e.type().is_not_nil());

      identifiers.push_back(e);
    }
  }
}

void cpp_typecheck_resolvet::apply_template_args(
  resolve_identifierst &identifiers,
  const cpp_template_args_non_tct &template_args,
  const cpp_typecheck_fargst &fargs)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    exprt e = old_id;
    apply_template_args(e, template_args, fargs);

    if(e.is_not_nil())
    {
      if(e.id()==ID_type)
        assert(e.type().is_not_nil());

      identifiers.push_back(e);
    }
  }
}

/// guess arguments of function templates
void cpp_typecheck_resolvet::guess_function_template_args(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    exprt e = guess_function_template_args(old_id, fargs);

    if(e.is_not_nil())
    {
      assert(e.id()!=ID_type);
      identifiers.push_back(e);
    }
  }

  disambiguate_functions(identifiers, fargs);

  // there should only be one left, or we have failed to disambiguate
  if(identifiers.size()==1)
  {
    // instantiate that one
    exprt e=*identifiers.begin();
    assert(e.id()==ID_template_function_instance);

    const symbolt &template_symbol=
      cpp_typecheck.lookup(e.type().get(ID_C_template));

    const cpp_template_args_tct &template_args=
      to_cpp_template_args_tc(e.type().find(ID_C_template_arguments));

    // Let's build the instance.

    const symbolt &new_symbol=
      cpp_typecheck.instantiate_template(
        source_location,
        template_symbol,
        template_args,
        template_args);

    identifiers.clear();
    identifiers.push_back(
      symbol_exprt(new_symbol.name, new_symbol.type));
  }
}

void cpp_typecheck_resolvet::remove_templates(
  resolve_identifierst &identifiers)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    if(!cpp_typecheck.follow(old_id.type()).get_bool(ID_is_template))
      identifiers.push_back(old_id);
  }
}

void cpp_typecheck_resolvet::remove_duplicates(
  resolve_identifierst &identifiers)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  std::set<irep_idt> ids;
  std::set<exprt> other;

  for(const auto &old_id : old_identifiers)
  {
    irep_idt id;

    if(old_id.id() == ID_symbol)
      id = to_symbol_expr(old_id).get_identifier();
    else if(old_id.id() == ID_type && old_id.type().id() == ID_struct_tag)
      id = to_struct_tag_type(old_id.type()).get_identifier();
    else if(old_id.id() == ID_type && old_id.type().id() == ID_union_tag)
      id = to_union_tag_type(old_id.type()).get_identifier();

    if(id=="")
    {
      if(other.insert(old_id).second)
        identifiers.push_back(old_id);
    }
    else
    {
      if(ids.insert(id).second)
        identifiers.push_back(old_id);
    }
  }
}

exprt cpp_typecheck_resolvet::convert_template_parameter(
  const cpp_idt &identifier)
{
#ifdef DEBUG
  std::cout << "RESOLVE MAP:" << std::endl;
  cpp_typecheck.template_map.print(std::cout);
#endif

  // look up the parameter in the template map
  exprt e=cpp_typecheck.template_map.lookup(identifier.identifier);

  if(e.is_nil() ||
     (e.id()==ID_type && e.type().is_nil()))
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error() << "internal error: template parameter "
                          << "without instance:\n"
                          << identifier << messaget::eom;
    throw 0;
  }

  e.add_source_location()=source_location;

  return e;
}

exprt cpp_typecheck_resolvet::convert_identifier(
  const cpp_idt &identifier,
  const cpp_typecheck_fargst &fargs)
{
  if(identifier.id_class==cpp_scopet::id_classt::TEMPLATE_PARAMETER)
    return convert_template_parameter(identifier);

  exprt e;

  if(identifier.is_member &&
     !identifier.is_constructor &&
     !identifier.is_static_member)
  {
    // a regular struct or union member

    const symbolt &compound_symbol=
      cpp_typecheck.lookup(identifier.class_identifier);

    assert(compound_symbol.type.id()==ID_struct ||
           compound_symbol.type.id()==ID_union);

    const struct_union_typet &struct_union_type=
      to_struct_union_type(compound_symbol.type);

    const exprt component=
      struct_union_type.get_component(identifier.identifier);

    const typet &type=component.type();
    assert(type.is_not_nil());

    if(identifier.id_class==cpp_scopet::id_classt::TYPEDEF)
    {
      e=type_exprt(type);
    }
    else if(identifier.id_class==cpp_scopet::id_classt::SYMBOL)
    {
      // A non-static, non-type member.
      // There has to be an object.
      e=exprt(ID_member);
      e.set(ID_component_name, identifier.identifier);
      e.add_source_location()=source_location;

      exprt object;
      object.make_nil();

      #if 0
      std::cout << "I: " << identifier.class_identifier
                << " "
                << cpp_typecheck.cpp_scopes.current_scope().
                    this_class_identifier << '\n';
      #endif

      const exprt &this_expr=
        original_scope->this_expr;

      if(fargs.has_object)
      {
        // the object is given to us in fargs
        assert(!fargs.operands.empty());
        object=fargs.operands.front();
      }
      else if(this_expr.is_not_nil())
      {
        // use this->...
        assert(this_expr.type().id()==ID_pointer);
        object=exprt(ID_dereference, this_expr.type().subtype());
        object.copy_to_operands(this_expr);
        object.type().set(ID_C_constant,
                          this_expr.type().subtype().get_bool(ID_C_constant));
        object.set(ID_C_lvalue, true);
        object.add_source_location()=source_location;
      }

      // check if the member can be applied to the object
      typet object_type=cpp_typecheck.follow(object.type());

      if(object_type.id()==ID_struct ||
         object_type.id()==ID_union)
      {
        if(!has_component_rec(
             to_struct_union_type(object_type),
             identifier.identifier,
             cpp_typecheck))
          object.make_nil(); // failed!
      }
      else
        object.make_nil();

      if(object.is_not_nil())
      {
        // we got an object
        e.move_to_operands(object);

        bool old_value=cpp_typecheck.disable_access_control;
        cpp_typecheck.disable_access_control=true;
        cpp_typecheck.typecheck_expr_member(e);
        cpp_typecheck.disable_access_control=old_value;
      }
      else
      {
        // this has to be a method or form a pointer-to-member expression
        if(identifier.is_method)
          e=cpp_symbol_expr(cpp_typecheck.lookup(identifier.identifier));
        else
        {
          e.id(ID_ptrmember);
          e.copy_to_operands(
            exprt("cpp-this", pointer_type(compound_symbol.type)));
          e.type() = type;
        }
      }
    }
  }
  else
  {
    const symbolt &symbol=
      cpp_typecheck.lookup(identifier.identifier);

    if(symbol.is_type)
    {
      e.make_nil();

      if(symbol.is_macro) // includes typedefs
      {
        e = type_exprt(symbol.type);
        assert(symbol.type.is_not_nil());
      }
      else if(symbol.type.id()==ID_c_enum)
      {
        e = type_exprt(c_enum_tag_typet(symbol.name));
      }
      else if(symbol.type.id() == ID_struct)
      {
        e = type_exprt(struct_tag_typet(symbol.name));
      }
      else if(symbol.type.id() == ID_union)
      {
        e = type_exprt(union_tag_typet(symbol.name));
      }
    }
    else if(symbol.is_macro)
    {
      e=symbol.value;
      assert(e.is_not_nil());
    }
    else
    {
      bool constant = symbol.type.get_bool(ID_C_constant);

      if(
        constant && symbol.value.is_not_nil() && is_number(symbol.type) &&
        symbol.value.id() == ID_constant)
      {
        e=symbol.value;
      }
      else
      {
        e=cpp_symbol_expr(symbol);
      }
    }
  }

  e.add_source_location()=source_location;

  return e;
}

void cpp_typecheck_resolvet::filter(
  resolve_identifierst &identifiers,
  const wantt want)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    bool match=false;

    switch(want)
    {
    case wantt::TYPE:
      match = (old_id.id() == ID_type);
      break;

    case wantt::VAR:
      match = (old_id.id() != ID_type);
      break;

    case wantt::BOTH:
      match=true;
      break;

    default:
      UNREACHABLE;
    }

    if(match)
      identifiers.push_back(old_id);
  }
}

void cpp_typecheck_resolvet::exact_match_functions(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
  if(!fargs.in_use)
    return;

  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  identifiers.clear();

  // put in the ones that match precisely
  for(const auto &old_id : old_identifiers)
  {
    unsigned distance;
    if(disambiguate_functions(old_id, distance, fargs))
      if(distance<=0)
        identifiers.push_back(old_id);
  }
}

void cpp_typecheck_resolvet::disambiguate_functions(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  // sort according to distance
  std::multimap<std::size_t, exprt> distance_map;

  for(const auto &old_id : old_identifiers)
  {
    unsigned args_distance;

    if(disambiguate_functions(old_id, args_distance, fargs))
    {
      std::size_t template_distance=0;

      if(old_id.type().get(ID_C_template) != "")
        template_distance = old_id.type()
                              .find(ID_C_template_arguments)
                              .find(ID_arguments)
                              .get_sub()
                              .size();

      // we give strong preference to functions that have
      // fewer template arguments
      std::size_t total_distance=
        // NOLINTNEXTLINE(whitespace/operators)
        1000*template_distance+args_distance;

      distance_map.insert({total_distance, old_id});
    }
  }

  identifiers.clear();

  // put in the top ones
  if(!distance_map.empty())
  {
    std::size_t distance=distance_map.begin()->first;

    for(std::multimap<std::size_t, exprt>::const_iterator
        it=distance_map.begin();
        it!=distance_map.end() && it->first==distance;
        it++)
      identifiers.push_back(it->second);
  }

  if(identifiers.size()>1 && fargs.in_use)
  {
    // try to further disambiguate functions

    for(resolve_identifierst::iterator
        it1=identifiers.begin();
        it1!=identifiers.end();
        it1++)
    {
      if(it1->type().id()!=ID_code)
        continue;

      const code_typet &f1=
        to_code_type(it1->type());

      for(resolve_identifierst::iterator it2=
          identifiers.begin();
          it2!=identifiers.end();
          ) // no it2++
      {
        if(it1 == it2)
        {
          it2++;
          continue;
        }

        if(it2->type().id()!=ID_code)
        {
          it2++;
          continue;
        }

        const code_typet &f2 =
          to_code_type(it2->type());

        // TODO: may fail when using ellipsis
        assert(f1.parameters().size() == f2.parameters().size());

        bool f1_better=true;
        bool f2_better=true;

        for(std::size_t i=0;
            i<f1.parameters().size() && (f1_better || f2_better);
            i++)
        {
          typet type1=f1.parameters()[i].type();
          typet type2=f2.parameters()[i].type();

          if(type1 == type2)
            continue;

          if(is_reference(type1) != is_reference(type2))
            continue;

          if(type1.id()==ID_pointer)
          {
            typet tmp=type1.subtype();
            type1=tmp;
          }

          if(type2.id()==ID_pointer)
          {
            typet tmp=type2.subtype();
            type2=tmp;
          }

          const typet &followed1=cpp_typecheck.follow(type1);
          const typet &followed2=cpp_typecheck.follow(type2);

          if(followed1.id() != ID_struct || followed2.id() != ID_struct)
            continue;

          const struct_typet &struct1=to_struct_type(followed1);
          const struct_typet &struct2=to_struct_type(followed2);

          if(f1_better && cpp_typecheck.subtype_typecast(struct1, struct2))
          {
            f2_better=false;
          }
          else if(f2_better && cpp_typecheck.subtype_typecast(struct2, struct1))
          {
            f1_better=false;
          }
        }

        resolve_identifierst::iterator prev_it=it2;
        it2++;

        if(f1_better && !f2_better)
          identifiers.erase(prev_it);
      }
    }
  }
}

void cpp_typecheck_resolvet::make_constructors(
  resolve_identifierst &identifiers)
{
  resolve_identifierst new_identifiers;

  for(const auto &identifier : identifiers)
  {
    if(identifier.id() != ID_type)
    {
      // already an expression
      new_identifiers.push_back(identifier);
      continue;
    }

    const typet &symbol_type = cpp_typecheck.follow(identifier.type());

    // is it a POD?

    if(cpp_typecheck.cpp_is_pod(symbol_type))
    {
      // there are two pod constructors:

      // 1. no arguments, default initialization
      {
        const code_typet t1({}, identifier.type());
        exprt pod_constructor1(ID_pod_constructor, t1);
        new_identifiers.push_back(pod_constructor1);
      }

      // 2. one argument, copy/conversion
      {
        const code_typet t2(
          {code_typet::parametert(identifier.type())}, identifier.type());
        exprt pod_constructor2(ID_pod_constructor, t2);
        new_identifiers.push_back(pod_constructor2);
      }

      // enums, in addition, can also be constructed from int
      if(symbol_type.id()==ID_c_enum_tag)
      {
        const code_typet t3(
          {code_typet::parametert(signed_int_type())}, identifier.type());
        exprt pod_constructor3(ID_pod_constructor, t3);
        new_identifiers.push_back(pod_constructor3);
      }
    }
    else if(symbol_type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(symbol_type);

      // go over components
      for(const auto &component : struct_type.components())
      {
        const typet &type=component.type();

        if(component.get_bool(ID_from_base))
          continue;

        if(
          type.id() == ID_code &&
          to_code_type(type).return_type().id() == ID_constructor)
        {
          const symbolt &symb =
            cpp_typecheck.lookup(component.get_name());
          exprt e=cpp_symbol_expr(symb);
          e.type()=type;
          new_identifiers.push_back(e);
        }
      }
    }
  }

  identifiers.swap(new_identifiers);
}

void cpp_typecheck_resolvet::resolve_argument(
  exprt &argument,
  const cpp_typecheck_fargst &fargs)
{
  if(argument.id() == ID_ambiguous) // could come from a template parameter
  {
    // this must be resolved in the template scope
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
    cpp_typecheck.cpp_scopes.go_to(*original_scope);

    argument = resolve(to_cpp_name(argument.type()), wantt::VAR, fargs, false);
  }
}

exprt cpp_typecheck_resolvet::do_builtin(
  const irep_idt &base_name,
  const cpp_typecheck_fargst &fargs,
  const cpp_template_args_non_tct &template_args)
{
  exprt dest;

  const cpp_template_args_non_tct::argumentst &arguments=
    template_args.arguments();

  if(base_name==ID_unsignedbv ||
     base_name==ID_signedbv)
  {
    if(arguments.size()!=1)
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << base_name << " expects one template argument, but got "
        << arguments.size() << messaget::eom;
      throw 0;
    }

    exprt argument=arguments.front(); // copy

    if(argument.id()==ID_type)
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << base_name << " expects one integer template argument, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    resolve_argument(argument, fargs);

    mp_integer i;
    if(to_integer(argument, i))
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error() << "template argument must be constant"
                            << messaget::eom;
      throw 0;
    }

    if(i<1)
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << "template argument must be greater than zero"
        << messaget::eom;
      throw 0;
    }

    dest=type_exprt(typet(base_name));
    dest.type().set(ID_width, integer2string(i));
  }
  else if(base_name==ID_fixedbv)
  {
    if(arguments.size()!=2)
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << base_name << " expects two template arguments, but got "
        << arguments.size() << messaget::eom;
      throw 0;
    }

    exprt argument0=arguments[0];
    resolve_argument(argument0, fargs);
    exprt argument1=arguments[1];
    resolve_argument(argument1, fargs);

    if(argument0.id()==ID_type)
    {
      cpp_typecheck.error().source_location=argument0.find_source_location();
      cpp_typecheck.error()
        << base_name << " expects two integer template arguments, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    if(argument1.id()==ID_type)
    {
      cpp_typecheck.error().source_location=argument1.find_source_location();
      cpp_typecheck.error()
        << base_name << " expects two integer template arguments, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    mp_integer width, integer_bits;

    if(to_integer(argument0, width))
    {
      cpp_typecheck.error().source_location=argument0.find_source_location();
      cpp_typecheck.error() << "template argument must be constant"
                            << messaget::eom;
      throw 0;
    }

    if(to_integer(argument1, integer_bits))
    {
      cpp_typecheck.error().source_location=argument1.find_source_location();
      cpp_typecheck.error() << "template argument must be constant"
                            << messaget::eom;
      throw 0;
    }

    if(width<1)
    {
      cpp_typecheck.error().source_location=argument0.find_source_location();
      cpp_typecheck.error()
        << "template argument must be greater than zero"
        << messaget::eom;
      throw 0;
    }

    if(integer_bits<0)
    {
      cpp_typecheck.error().source_location=argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be greater or equal zero"
        << messaget::eom;
      throw 0;
    }

    if(integer_bits>width)
    {
      cpp_typecheck.error().source_location=argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be smaller or equal width"
        << messaget::eom;
      throw 0;
    }

    dest=type_exprt(typet(base_name));
    dest.type().set(ID_width, integer2string(width));
    dest.type().set(ID_integer_bits, integer2string(integer_bits));
  }
  else if(base_name==ID_integer)
  {
    if(!arguments.empty())
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << base_name << " expects no template arguments"
        << messaget::eom;
      throw 0;
    }

    dest=type_exprt(typet(base_name));
  }
  else if(has_prefix(id2string(base_name), "constant_infinity"))
  {
    // ok, but type missing
    dest=exprt(ID_infinity, size_type());
  }
  else if(base_name=="dump_scopes")
  {
    dest=exprt(ID_constant, typet(ID_empty));
    cpp_typecheck.warning() << "Scopes in location "
                            << source_location << messaget::eom;
    cpp_typecheck.cpp_scopes.get_root_scope().print(
      cpp_typecheck.warning());
  }
  else if(base_name=="current_scope")
  {
    dest=exprt(ID_constant, typet(ID_empty));
    cpp_typecheck.warning() << "Scope in location " << source_location
                            << ": " << original_scope->prefix
                            << messaget::eom;
  }
  else if(base_name == ID_size_t)
  {
    dest=type_exprt(size_type());
  }
  else if(base_name == ID_ssize_t)
  {
    dest=type_exprt(signed_size_type());
  }
  else
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error() << "unknown built-in identifier: "
                          << base_name << messaget::eom;
    throw 0;
  }

  return dest;
}

/// \par parameters: a cpp_name
/// \return a base_name, and potentially template arguments for the base name;
///   as side-effect, we got to the right scope
cpp_scopet &cpp_typecheck_resolvet::resolve_scope(
  const cpp_namet &cpp_name,
  irep_idt &base_name,
  cpp_template_args_non_tct &template_args)
{
  assert(!cpp_name.get_sub().empty());

  original_scope=&cpp_typecheck.cpp_scopes.current_scope();
  source_location=cpp_name.source_location();

  irept::subt::const_iterator pos=cpp_name.get_sub().begin();

  bool recursive=true;

  // check if we need to go to the root scope
  if(pos->id()=="::")
  {
    pos++;
    cpp_typecheck.cpp_scopes.go_to_root_scope();
    recursive=false;
  }

  std::string final_base_name="";
  template_args.make_nil();

  while(pos!=cpp_name.get_sub().end())
  {
    if(pos->id()==ID_name)
      final_base_name+=pos->get_string(ID_identifier);
    else if(pos->id()==ID_template_args)
      template_args=to_cpp_template_args_non_tc(*pos);
    else if(pos->id()=="::")
    {
      if(template_args.is_not_nil())
      {
        const auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED,
          cpp_idt::id_classt::TEMPLATE);

#ifdef DEBUG
        std::cout << "S: "
                  << cpp_typecheck.cpp_scopes.current_scope().identifier
                  << '\n';
        cpp_typecheck.cpp_scopes.current_scope().print(std::cout);
        std::cout << "X: " << id_set.size() << '\n';
#endif
        struct_tag_typet instance =
          disambiguate_template_classes(final_base_name, id_set, template_args);

        instance.add_source_location()=source_location;

        // the "::" triggers template elaboration
        cpp_typecheck.elaborate_class_template(instance);

        cpp_typecheck.cpp_scopes.go_to(
          cpp_typecheck.cpp_scopes.get_scope(instance.get_identifier()));

        template_args.make_nil();
      }
      else
      {
        auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED);

        filter_for_named_scopes(id_set);

        if(id_set.empty())
        {
          cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
          cpp_typecheck.error().source_location=source_location;
          cpp_typecheck.error() << "scope `" << final_base_name
                                << "' not found" << messaget::eom;
          throw 0;
        }
        else if(id_set.size()>=2)
        {
          cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
          cpp_typecheck.error().source_location=source_location;
          cpp_typecheck.error() << "scope `"
                                << final_base_name << "' is ambiguous"
                                << messaget::eom;
          throw 0;
        }

        assert(id_set.size()==1);

        cpp_typecheck.cpp_scopes.go_to(**id_set.begin());

        // the "::" triggers template elaboration
        if(!cpp_typecheck.cpp_scopes.current_scope().class_identifier.empty())
        {
          struct_tag_typet instance(
            cpp_typecheck.cpp_scopes.current_scope().class_identifier);
          cpp_typecheck.elaborate_class_template(instance);
        }
      }

      // we start from fresh
      final_base_name.clear();
    }
    else if(pos->id()==ID_operator)
    {
      final_base_name+="operator";

      irept::subt::const_iterator next=pos+1;
      assert(next != cpp_name.get_sub().end());

      if(
        next->id() == ID_cpp_name || next->id() == ID_pointer ||
        next->id() == ID_int || next->id() == ID_char ||
        next->id() == ID_c_bool || next->id() == ID_merged_type)
      {
        // it's a cast operator
        irept next_ir=*next;
        typet op_name;
        op_name.swap(next_ir);
        cpp_typecheck.typecheck_type(op_name);
        final_base_name+="("+cpp_type2name(op_name)+")";
        pos++;
      }
    }
    else
      final_base_name+=pos->id_string();

    pos++;
  }

  base_name=final_base_name;

  return cpp_typecheck.cpp_scopes.current_scope();
}

/// disambiguate partial specialization
struct_tag_typet cpp_typecheck_resolvet::disambiguate_template_classes(
  const irep_idt &base_name,
  const cpp_scopest::id_sett &id_set,
  const cpp_template_args_non_tct &full_template_args)
{
  if(id_set.empty())
  {
    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error() << "template scope `" << base_name
                          << "' not found" << messaget::eom;
    throw 0;
  }

  std::set<irep_idt> primary_templates;

  for(const auto &id_ptr : id_set)
  {
    const irep_idt id = id_ptr->identifier;
    const symbolt &s=cpp_typecheck.lookup(id);
    if(!s.type.get_bool(ID_is_template))
      continue;
    const cpp_declarationt &cpp_declaration=to_cpp_declaration(s.type);
    if(!cpp_declaration.is_class_template())
      continue;
    irep_idt specialization_of=cpp_declaration.get_specialization_of();
    if(specialization_of!="")
      primary_templates.insert(specialization_of);
    else
      primary_templates.insert(id);
  }

  assert(!primary_templates.empty());

  if(primary_templates.size()>=2)
  {
    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error() << "template scope `" << base_name
                          << "' is ambiguous" << messaget::eom;
    throw 0;
  }

  const symbolt &primary_template_symbol=
    cpp_typecheck.lookup(*primary_templates.begin());

  // We typecheck the template arguments in the context
  // of the original scope!
  cpp_template_args_tct full_template_args_tc;

  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.cpp_scopes.go_to(*original_scope);

    // use template type of 'primary template'
    full_template_args_tc=
      cpp_typecheck.typecheck_template_args(
        source_location,
        primary_template_symbol,
        full_template_args);
    // go back to where we used to be
  }

  // find any matches

  std::vector<matcht> matches;

  // the baseline
  matches.push_back(
    matcht(full_template_args_tc, full_template_args_tc,
           primary_template_symbol.name));

  for(const auto &id_ptr : id_set)
  {
    const irep_idt id = id_ptr->identifier;
    const symbolt &s=cpp_typecheck.lookup(id);

    if(s.type.get(ID_specialization_of).empty())
      continue;

    const cpp_declarationt &cpp_declaration=
      to_cpp_declaration(s.type);

    const cpp_template_args_non_tct &partial_specialization_args=
      cpp_declaration.partial_specialization_args();

    // alright, set up template arguments as 'unassigned'

    cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.template_map.build_unassigned(
      cpp_declaration.template_type());

    // iterate over template instance
    assert(full_template_args_tc.arguments().size()==
           partial_specialization_args.arguments().size());

    // we need to do this in the right scope

    cpp_scopet *template_scope=
      static_cast<cpp_scopet *>(
        cpp_typecheck.cpp_scopes.id_map[id]);

    if(template_scope==nullptr)
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error() << "template identifier: " << id << '\n'
                            << "class template instantiation error"
                            << messaget::eom;
      throw 0;
    }

    // enter the scope of the template
    cpp_typecheck.cpp_scopes.go_to(*template_scope);

    for(std::size_t i=0; i<full_template_args_tc.arguments().size(); i++)
    {
      if(full_template_args_tc.arguments()[i].id()==ID_type)
        guess_template_args(partial_specialization_args.arguments()[i].type(),
                            full_template_args_tc.arguments()[i].type());
      else
        guess_template_args(partial_specialization_args.arguments()[i],
                            full_template_args_tc.arguments()[i]);
    }

    // see if that has worked out

    cpp_template_args_tct guessed_template_args=
      cpp_typecheck.template_map.build_template_args(
        cpp_declaration.template_type());

    if(!guessed_template_args.has_unassigned())
    {
      // check: we can now typecheck the partial_specialization_args

      cpp_template_args_tct partial_specialization_args_tc=
        cpp_typecheck.typecheck_template_args(
          source_location,
          primary_template_symbol,
          partial_specialization_args);

      // if these match the arguments, we have a match

      assert(partial_specialization_args_tc.arguments().size()==
             full_template_args_tc.arguments().size());

      if(partial_specialization_args_tc==
         full_template_args_tc)
      {
        matches.push_back(matcht(
          guessed_template_args, full_template_args_tc, id));
      }
    }
  }

  assert(!matches.empty());

  std::sort(matches.begin(), matches.end());

  #if 0
  for(std::vector<matcht>::const_iterator
      m_it=matches.begin();
      m_it!=matches.end();
      m_it++)
  {
    std::cout << "M: " << m_it->cost
              << " " << m_it->id << '\n';
  }

  std::cout << '\n';
  #endif

  const matcht &match=*matches.begin();

  const symbolt &choice=
    cpp_typecheck.lookup(match.id);

  #if 0
  // build instance
  const symbolt &instance=
    cpp_typecheck.instantiate_template(
      source_location,
      choice,
      match.specialization_args,
      match.full_args);

  if(instance.type.id()!=ID_struct)
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.str << "template `"
                      << base_name << "' is not a class";
    throw 0;
  }

  struct_tag_typet result(instance.name);
  result.add_source_location()=source_location;

  return result;
  #else

  // build instance
  const symbolt &instance=
    cpp_typecheck.class_template_symbol(
      source_location,
      choice,
      match.specialization_args,
      match.full_args);

  struct_tag_typet result(instance.name);
  result.add_source_location()=source_location;

  return result;
  #endif
}

cpp_scopet &cpp_typecheck_resolvet::resolve_namespace(
  const cpp_namet &cpp_name)
{
  irep_idt base_name;
  cpp_template_args_non_tct template_args;
  template_args.make_nil();

  cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
  resolve_scope(cpp_name, base_name, template_args);

  bool qualified=cpp_name.is_qualified();

  auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
    base_name, qualified ? cpp_scopet::QUALIFIED : cpp_scopet::RECURSIVE);

  filter_for_namespaces(id_set);

  if(id_set.empty())
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error()
      << "namespace `"
      << base_name << "' not found" << messaget::eom;
    throw 0;
  }
  else if(id_set.size()==1)
  {
    cpp_idt &id=**id_set.begin();
    return (cpp_scopet &)id;
  }
  else
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error()
      << "namespace `"
      << base_name << "' is ambiguous" << messaget::eom;
    throw 0;
  }
}

void cpp_typecheck_resolvet::show_identifiers(
  const irep_idt &base_name,
  const resolve_identifierst &identifiers,
  std::ostream &out)
{
  for(const auto &id_expr : identifiers)
  {
    out << "  ";

    if(id_expr.id()==ID_type)
    {
      out << "type " << cpp_typecheck.to_string(id_expr.type());
    }
    else
    {
      irep_idt id;

      if(id_expr.type().get_bool(ID_is_template))
        out << "template ";

      if(id_expr.id()==ID_member)
      {
        out << "member ";
        id="."+id2string(base_name);
      }
      else if(id_expr.id() == ID_pod_constructor)
      {
        out << "constructor ";
        id="";
      }
      else if(id_expr.id()==ID_template_function_instance)
      {
        out << "symbol ";
      }
      else
      {
        out << "symbol ";
        id=cpp_typecheck.to_string(id_expr);
      }

      if(id_expr.type().get_bool(ID_is_template))
      {
      }
      else if(id_expr.type().id()==ID_code)
      {
        const code_typet &code_type=to_code_type(id_expr.type());
        const typet &return_type=code_type.return_type();
        const code_typet::parameterst &parameters=code_type.parameters();
        out << cpp_typecheck.to_string(return_type);
        out << " " << id << "(";

        bool first = true;

        for(const auto &parameter : parameters)
        {
          const typet &parameter_type = parameter.type();

          if(first)
            first = false;
          else
            out << ", ";

          out << cpp_typecheck.to_string(parameter_type);
        }

        if(code_type.has_ellipsis())
        {
          if(!parameters.empty())
            out << ", ";
          out << "...";
        }

        out << ")";
      }
      else
        out << id << ": " << cpp_typecheck.to_string(id_expr.type());

      if(id_expr.id()==ID_symbol)
      {
        const symbolt &symbol=cpp_typecheck.lookup(to_symbol_expr(id_expr));
        out << " (" << symbol.location << ")";
      }
      else if(id_expr.id()==ID_template_function_instance)
      {
        const symbolt &symbol=
          cpp_typecheck.lookup(id_expr.type().get(ID_C_template));
        out << " (" << symbol.location << ")";
      }
    }

    out << '\n';
  }
}

exprt cpp_typecheck_resolvet::resolve(
  const cpp_namet &cpp_name,
  const wantt want,
  const cpp_typecheck_fargst &fargs,
  bool fail_with_exception)
{
  irep_idt base_name;
  cpp_template_args_non_tct template_args;
  template_args.make_nil();

  original_scope=&cpp_typecheck.cpp_scopes.current_scope();
  cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

  // this changes the scope
  resolve_scope(cpp_name, base_name, template_args);

#ifdef DEBUG
  std::cout << "base name: " << base_name << std::endl;
  std::cout << "template args: " << template_args.pretty() << std::endl;
  std::cout << "original-scope: " << original_scope->prefix << std::endl;
  std::cout << "scope: "
            << cpp_typecheck.cpp_scopes.current_scope().prefix << std::endl;
#endif

  bool qualified=cpp_name.is_qualified();

  // do __CPROVER scope
  if(qualified)
  {
    if(cpp_typecheck.cpp_scopes.current_scope().identifier=="__CPROVER")
      return do_builtin(base_name, fargs, template_args);
  }
  else
  {
    if(base_name=="__func__" ||
       base_name=="__FUNCTION__" ||
       base_name=="__PRETTY_FUNCTION__")
    {
      // __func__ is an ANSI-C standard compliant hack to get the function name
      // __FUNCTION__ and __PRETTY_FUNCTION__ are GCC-specific
      string_constantt s(source_location.get_function());
      s.add_source_location()=source_location;
      return std::move(s);
    }
  }

  cpp_scopest::id_sett id_set;

  cpp_scopet::lookup_kindt lookup_kind=
    qualified?cpp_scopet::QUALIFIED:cpp_scopet::RECURSIVE;

  if(template_args.is_nil())
  {
    id_set =
      cpp_typecheck.cpp_scopes.current_scope().lookup(base_name, lookup_kind);

    if(id_set.empty() && !cpp_typecheck.builtin_factory(base_name))
    {
      cpp_idt &builtin_id =
        cpp_typecheck.cpp_scopes.get_root_scope().insert(base_name);
      builtin_id.identifier = base_name;
      builtin_id.id_class = cpp_idt::id_classt::SYMBOL;

      id_set.insert(&builtin_id);
    }
  }
  else
    id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
      base_name, lookup_kind, cpp_idt::id_classt::TEMPLATE);

  // Argument-dependent name lookup
  #if 0
  // not clear what this is good for
  if(!qualified && !fargs.has_object)
    resolve_with_arguments(id_set, base_name, fargs);
  #endif

  if(id_set.empty())
  {
    if(!fail_with_exception)
      return nil_exprt();

    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location=source_location;

    if(qualified)
    {
      cpp_typecheck.error()
        << "symbol `"
        << base_name << "' not found";

      if(cpp_typecheck.cpp_scopes.current_scope().is_root_scope())
        cpp_typecheck.error() << " in root scope";
      else
        cpp_typecheck.error() << " in scope `"
                              << cpp_typecheck.cpp_scopes.current_scope().prefix
                              << "'";
    }
    else
    {
      cpp_typecheck.error()
        << "symbol `"
        << base_name << "' is unknown";
    }

    cpp_typecheck.error() << messaget::eom;
    // cpp_typecheck.cpp_scopes.get_root_scope().print(std::cout);
    // cpp_typecheck.cpp_scopes.current_scope().print(std::cout);
    throw 0;
  }

  resolve_identifierst identifiers;

  if(template_args.is_not_nil())
  {
    // first figure out if we are doing functions/methods or
    // classes
    bool have_classes=false, have_methods=false;

    for(const auto &id_ptr : id_set)
    {
      const irep_idt id = id_ptr->identifier;
      const symbolt &s=cpp_typecheck.lookup(id);
      assert(s.type.get_bool(ID_is_template));
      if(to_cpp_declaration(s.type).is_class_template())
        have_classes=true;
      else
        have_methods=true;
    }

    if(want==wantt::BOTH && have_classes && have_methods)
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << "template symbol `"
        << base_name << "' is ambiguous" << messaget::eom;
      throw 0;
    }

    if(want==wantt::TYPE || have_classes)
    {
      typet instance=
        disambiguate_template_classes(base_name, id_set, template_args);

      cpp_typecheck.elaborate_class_template(instance);

      identifiers.push_back(exprt(ID_type, instance));
    }
    else
    {
      // methods and functions
      convert_identifiers(
        id_set, fargs, identifiers);

      apply_template_args(
        identifiers, template_args, fargs);
    }
  }
  else
  {
    convert_identifiers(
      id_set, fargs, identifiers);
  }

  // change types into constructors if we want a constructor
  if(want==wantt::VAR)
    make_constructors(identifiers);

  filter(identifiers, want);

  #if 0
  std::cout << "P0 " << base_name << " " << identifiers.size() << "\n";
  show_identifiers(base_name, identifiers, std::cout);
  std::cout << "\n";
  #endif

  exprt result;

  // We disambiguate functions
  resolve_identifierst new_identifiers=identifiers;

  remove_templates(new_identifiers);

  #if 0
  std::cout << "P1 " << base_name << " " << new_identifiers.size() << "\n";
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << "\n";
  #endif

  // we only want _exact_ matches, without templates!
  exact_match_functions(new_identifiers, fargs);

  #if 0
  std::cout << "P2 " << base_name << " " << new_identifiers.size() << "\n";
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << "\n";
  #endif

  // no exact matches? Try again with function template guessing.
  if(new_identifiers.empty())
  {
    new_identifiers=identifiers;

    if(template_args.is_nil())
    {
      guess_function_template_args(new_identifiers, fargs);

      if(new_identifiers.empty())
        new_identifiers=identifiers;
    }

    disambiguate_functions(new_identifiers, fargs);

    #if 0
    std::cout << "P3 " << base_name << " " << new_identifiers.size() << "\n";
    show_identifiers(base_name, new_identifiers, std::cout);
    std::cout << "\n";
    #endif
  }

  remove_duplicates(new_identifiers);

  #if 0
  std::cout << "P4 " << base_name << " " << new_identifiers.size() << "\n";
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << "\n";
  #endif

  if(new_identifiers.size()==1)
  {
    result=*new_identifiers.begin();
  }
  else
  {
    // nothing or too many
    if(!fail_with_exception)
      return nil_exprt();

    if(new_identifiers.empty())
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << "found no match for symbol `" << base_name
        << "', candidates are:\n";
      show_identifiers(base_name, identifiers, cpp_typecheck.error());
    }
    else
    {
      cpp_typecheck.error().source_location=source_location;
      cpp_typecheck.error()
        << "symbol `" << base_name
        << "' does not uniquely resolve:\n";
      show_identifiers(base_name, new_identifiers, cpp_typecheck.error());

      #if 0
      exprt e1=*new_identifiers.begin();
      exprt e2=*(++new_identifiers.begin());
      cpp_typecheck.str << "e1==e2: " << (e1==e2) << '\n';
      cpp_typecheck.str << "e1.type==e2.type: " << (e1.type()==e2.type())
                        << '\n';
      cpp_typecheck.str << "e1.id()==e2.id(): " << (e1.id()==e2.id())
                        << '\n';
      cpp_typecheck.str << "e1.iden==e2.iden: "
                        << (e1.get(ID_identifier)==e2.get(ID_identifier))
                        << '\n';
      cpp_typecheck.str << "e1.iden:: " << e1.get(ID_identifier) << '\n';
      cpp_typecheck.str << "e2.iden:: " << e2.get(ID_identifier) << '\n';
      #endif
    }

    if(fargs.in_use)
    {
      cpp_typecheck.error() << "\nargument types:\n";

      for(const auto &op : fargs.operands)
      {
        cpp_typecheck.error()
          << "  " << cpp_typecheck.to_string(op.type()) << '\n';
      }
    }

    if(!cpp_typecheck.instantiation_stack.empty())
    {
      cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    }

    cpp_typecheck.error() << messaget::eom;
    throw 0;
  }

  // we do some checks before we return
  if(result.get_bool(ID_C_not_accessible))
  {
    #if 0
    if(!fail_with_exception)
      return nil_exprt();

    cpp_typecheck.error().source_location=result.source_location());
    cpp_typecheck.str
      << "error: member `" << result.get(ID_component_name)
      << "' is not accessible";
    throw 0;
    #endif
  }

  switch(want)
  {
  case wantt::VAR:
    if(result.id()==ID_type && !cpp_typecheck.cpp_is_pod(result.type()))
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.error().source_location=source_location;

      cpp_typecheck.error()
        << "error: expected expression, but got type `"
        << cpp_typecheck.to_string(result.type()) << "'"
        << messaget::eom;

      throw 0;
    }
    break;

  case wantt::TYPE:
    if(result.id()!=ID_type)
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.error().source_location=source_location;

      cpp_typecheck.error()
        << "error: expected type, but got expression `"
        << cpp_typecheck.to_string(result) << "'" << messaget::eom;

      throw 0;
    }
    break;

  default:
    {
    }
  }

  return result;
}

void cpp_typecheck_resolvet::guess_template_args(
  const exprt &template_expr,
  const exprt &desired_expr)
{
  if(template_expr.id()==ID_cpp_name)
  {
    const cpp_namet &cpp_name=
      to_cpp_name(template_expr);

    if(!cpp_name.is_qualified())
    {
      cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

      cpp_template_args_non_tct template_args;
      irep_idt base_name;
      resolve_scope(cpp_name, base_name, template_args);

      const auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
        base_name, cpp_scopet::RECURSIVE);

      // alright, rummage through these
      for(const auto &id_ptr : id_set)
      {
        const cpp_idt &id = *id_ptr;
        // template parameter?
        if(id.id_class==cpp_idt::id_classt::TEMPLATE_PARAMETER)
        {
          // see if unassigned
          exprt &e=cpp_typecheck.template_map.expr_map[id.identifier];
          if(e.id()==ID_unassigned)
          {
            typet old_type=e.type();
            e=desired_expr;
            if(e.type()!=old_type)
              e.make_typecast(old_type);
          }
        }
      }
    }
  }
}

void cpp_typecheck_resolvet::guess_template_args(
  const typet &template_type,
  const typet &desired_type)
{
  // look at
  // http://publib.boulder.ibm.com/infocenter/comphelp/v8v101/topic/
  //  com.ibm.xlcpp8a.doc/language/ref/template_argument_deduction.htm

  // T
  // const T
  // volatile T
  // T&
  // T*
  // T[10]
  // A<T>
  // C(*)(T)
  // T(*)()
  // T(*)(U)
  // T C::*
  // C T::*
  // T U::*
  // T (C::*)()
  // C (T::*)()
  // D (C::*)(T)
  // C (T::*)(U)
  // T (C::*)(U)
  // T (U::*)()
  // T (U::*)(V)
  // E[10][i]
  // B<i>
  // TT<T>
  // TT<i>
  // TT<C>

  #if 0
  std::cout << "TT: " << template_type.pretty() << '\n';
  std::cout << "DT: " << desired_type.pretty() << '\n';
  #endif

  if(template_type.id()==ID_cpp_name)
  {
    // we only care about cpp_names that are template parameters!
    const cpp_namet &cpp_name=to_cpp_name(template_type);

    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    if(cpp_name.has_template_args())
    {
      // this could be something like my_template<T>, and we need
      // to match 'T'. Then 'desired_type' has to be a template instance.

      // TODO
    }
    else
    {
      // template parameters aren't qualified
      if(!cpp_name.is_qualified())
      {
        irep_idt base_name;
        cpp_template_args_non_tct template_args;
        resolve_scope(cpp_name, base_name, template_args);

        const auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          base_name, cpp_scopet::RECURSIVE);

        // alright, rummage through these
        for(const auto &id_ptr : id_set)
        {
          const cpp_idt &id = *id_ptr;

          // template argument?
          if(id.id_class==cpp_idt::id_classt::TEMPLATE_PARAMETER)
          {
            // see if unassigned
            typet &t=cpp_typecheck.template_map.type_map[id.identifier];
            if(t.id()==ID_unassigned)
            {
              t=desired_type;

              // remove const, volatile (these can be added in the call)
              t.remove(ID_C_constant);
              t.remove(ID_C_volatile);
              #if 0
              std::cout << "ASSIGN " << id.identifier << " := "
                        << cpp_typecheck.to_string(desired_type) << '\n';
              #endif
            }
          }
        }
      }
    }
  }
  else if(template_type.id()==ID_merged_type)
  {
    // look at subtypes
    for(const auto &t : to_merged_type(template_type).subtypes())
    {
      guess_template_args(t, desired_type);
    }
  }
  else if(is_reference(template_type) ||
          is_rvalue_reference(template_type))
  {
    guess_template_args(template_type.subtype(), desired_type);
  }
  else if(template_type.id()==ID_pointer)
  {
    if(desired_type.id() == ID_pointer)
      guess_template_args(template_type.subtype(), desired_type.subtype());
  }
  else if(template_type.id()==ID_array)
  {
    if(desired_type.id() == ID_array)
    {
      // look at subtype first
      guess_template_args(template_type.subtype(), desired_type.subtype());

      // size (e.g., buffer size guessing)
      guess_template_args(
        to_array_type(template_type).size(),
        to_array_type(desired_type).size());
    }
  }
}

/// Guess template arguments for function templates
exprt cpp_typecheck_resolvet::guess_function_template_args(
  const exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  typet tmp = cpp_typecheck.follow(expr.type());

  if(!tmp.get_bool(ID_is_template))
    return nil_exprt(); // not a template

  assert(expr.id()==ID_symbol);

  // a template is always a declaration
  const cpp_declarationt &cpp_declaration=
    to_cpp_declaration(tmp);

  // Class templates require explicit template arguments,
  // no guessing!
  if(cpp_declaration.is_class_template())
    return nil_exprt();

  // we need function arguments for guessing
  if(fargs.operands.empty())
    return nil_exprt(); // give up

  // We need to guess in the case of function templates!

  irep_idt template_identifier=
    to_symbol_expr(expr).get_identifier();

  const symbolt &template_symbol=
    cpp_typecheck.lookup(template_identifier);

  // alright, set up template arguments as 'unassigned'

  cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);

  cpp_typecheck.template_map.build_unassigned(
    cpp_declaration.template_type());

  // there should be exactly one declarator
  assert(cpp_declaration.declarators().size()==1);

  const cpp_declaratort &function_declarator=
    cpp_declaration.declarators().front();

  // and that needs to have function type
  if(function_declarator.type().id()!=ID_function_type)
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error()
      << "expected function type for function template"
      << messaget::eom;
    throw 0;
  }

  cpp_save_scopet cpp_saved_scope(cpp_typecheck.cpp_scopes);

  // we need the template scope
  cpp_scopet *template_scope=
    static_cast<cpp_scopet *>(
      cpp_typecheck.cpp_scopes.id_map[template_identifier]);

  if(template_scope==nullptr)
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error() << "template identifier: "
                          << template_identifier << '\n'
                          << "function template instantiation error"
                          << messaget::eom;
    throw 0;
  }

  // enter the scope of the template
  cpp_typecheck.cpp_scopes.go_to(*template_scope);

  // walk through the function parameters
  const irept::subt &parameters=
    function_declarator.type().find(ID_parameters).get_sub();

  exprt::operandst::const_iterator it=fargs.operands.begin();
  for(const auto &parameter : parameters)
  {
    if(it==fargs.operands.end())
      break;

    if(parameter.id()==ID_cpp_declaration)
    {
      const cpp_declarationt &arg_declaration=
        to_cpp_declaration(parameter);

      // again, there should be one declarator
      assert(arg_declaration.declarators().size()==1);

      // turn into type
      typet arg_type=
        arg_declaration.declarators().front().
          merge_type(arg_declaration.type());

      // We only convert the arg_type,
      // and don't typecheck it -- that could cause all
      // sorts of trouble.
      cpp_convert_plain_type(arg_type);

      guess_template_args(arg_type, it->type());
    }

    ++it;
  }

  // see if that has worked out

  cpp_template_args_tct template_args=
    cpp_typecheck.template_map.build_template_args(
      cpp_declaration.template_type());

  if(template_args.has_unassigned())
    return nil_exprt(); // give up

  // Build the type of the function.

  typet function_type=
    function_declarator.merge_type(cpp_declaration.type());

  cpp_typecheck.typecheck_type(function_type);

  // Remember that this was a template

  function_type.set(ID_C_template, template_symbol.name);
  function_type.set(ID_C_template_arguments, template_args);

  // Seems we got an instance for all parameters. Let's return that.

  exprt template_function_instance(
    ID_template_function_instance, function_type);

  return template_function_instance;
}

void cpp_typecheck_resolvet::apply_template_args(
  exprt &expr,
  const cpp_template_args_non_tct &template_args_non_tc,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.id()!=ID_symbol)
    return; // templates are always symbols

  const symbolt &template_symbol =
    cpp_typecheck.lookup(to_symbol_expr(expr).get_identifier());

  if(!template_symbol.type.get_bool(ID_is_template))
    return;

  #if 0
  if(template_args_non_tc.is_nil())
  {
    // no arguments, need to guess
    guess_function_template_args(expr, fargs);
    return;
  }
  #endif

  // We typecheck the template arguments in the context
  // of the original scope!
  cpp_template_args_tct template_args_tc;

  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.cpp_scopes.go_to(*original_scope);

    template_args_tc=
      cpp_typecheck.typecheck_template_args(
        source_location,
        template_symbol,
        template_args_non_tc);
    // go back to where we used to be
  }

  // We never try 'unassigned' template arguments.
  if(template_args_tc.has_unassigned())
    UNREACHABLE;

  // a template is always a declaration
  const cpp_declarationt &cpp_declaration=
    to_cpp_declaration(template_symbol.type);

  // is it a class template or function template?
  if(cpp_declaration.is_class_template())
  {
    const symbolt &new_symbol=
      cpp_typecheck.instantiate_template(
        source_location,
        template_symbol,
        template_args_tc,
        template_args_tc);

    expr = type_exprt(struct_tag_typet(new_symbol.name));
    expr.add_source_location()=source_location;
  }
  else
  {
    // must be a function, maybe method
    const symbolt &new_symbol=
      cpp_typecheck.instantiate_template(
        source_location,
        template_symbol,
        template_args_tc,
        template_args_tc);

    // check if it is a method
    const code_typet &code_type=to_code_type(new_symbol.type);

    if(!code_type.parameters().empty() &&
        code_type.parameters()[0].get(ID_C_base_name)==ID_this)
    {
      // do we have an object?
      if(fargs.has_object)
      {
        const symbolt &type_symb=
          cpp_typecheck.lookup(
            fargs.operands.begin()->type().get(ID_identifier));

        assert(type_symb.type.id()==ID_struct);

        const struct_typet &struct_type=
          to_struct_type(type_symb.type);

        DATA_INVARIANT(struct_type.has_component(new_symbol.name),
                       "method should exist in struct");

        member_exprt member(
          *fargs.operands.begin(),
          new_symbol.name,
          code_type);
        member.add_source_location()=source_location;
        expr.swap(member);
        return;
      }
    }

    expr=cpp_symbol_expr(new_symbol);
    expr.add_source_location()=source_location;
  }
}

bool cpp_typecheck_resolvet::disambiguate_functions(
  const exprt &expr,
  unsigned &args_distance,
  const cpp_typecheck_fargst &fargs)
{
  args_distance=0;

  if(expr.type().id()!=ID_code || !fargs.in_use)
    return true;

  const code_typet &type=to_code_type(expr.type());

  if(expr.id()==ID_member ||
     type.return_type().id() == ID_constructor)
  {
    // if it's a member, but does not have an object yet,
    // we add one
    if(!fargs.has_object)
    {
      const code_typet::parameterst &parameters=type.parameters();
      const code_typet::parametert &parameter=parameters.front();

      assert(parameter.get(ID_C_base_name)==ID_this);

      if(type.return_type().id() == ID_constructor)
      {
        // it's a constructor
        const typet &object_type=parameter.type().subtype();
        symbol_exprt object(object_type);
        object.set(ID_C_lvalue, true);

        cpp_typecheck_fargst new_fargs(fargs);
        new_fargs.add_object(object);
        return new_fargs.match(type, args_distance, cpp_typecheck);
      }
      else
      {
        if(
          expr.type().get_bool(ID_C_is_operator) &&
          fargs.operands.size() == parameters.size())
        {
          return fargs.match(type, args_distance, cpp_typecheck);
        }

        cpp_typecheck_fargst new_fargs(fargs);
        new_fargs.add_object(expr.op0());

        return new_fargs.match(type, args_distance, cpp_typecheck);
      }
    }
  }
  else if(fargs.has_object)
  {
    // if it's not a member then we shall remove the object
    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.remove_object();

    return new_fargs.match(type, args_distance, cpp_typecheck);
  }

  return fargs.match(type, args_distance, cpp_typecheck);
}

void cpp_typecheck_resolvet::filter_for_named_scopes(
  cpp_scopest::id_sett &id_set)
{
  cpp_scopest::id_sett new_set;

  // std::cout << "FILTER\n";

  // We only want scopes!
  for(const auto &id_ptr : id_set)
  {
    cpp_idt &id = *id_ptr;

    if(id.is_class() || id.is_enum() || id.is_namespace())
    {
      // std::cout << "X1\n";
      assert(id.is_scope);
      new_set.insert(&id);
    }
    else if(id.is_typedef())
    {
      // std::cout << "X2\n";
      irep_idt identifier=id.identifier;

      if(id.is_member)
        continue;

      while(true)
      {
        const symbolt &symbol=cpp_typecheck.lookup(identifier);
        assert(symbol.is_type);

        // todo? maybe do enum here, too?
        if(symbol.type.id()==ID_struct)
        {
          // this is a scope, too!
          cpp_idt &class_id=
            cpp_typecheck.cpp_scopes.get_id(identifier);

          assert(class_id.is_scope);
          new_set.insert(&class_id);
          break;
        }
        else
          break;
      }
    }
    else if(id.id_class==cpp_scopet::id_classt::TEMPLATE)
    {
      // std::cout << "X3\n";
      #if 0
      const symbolt &symbol=
        cpp_typecheck.lookup(id.identifier);

      // Template struct? Really needs arguments to be a scope!
      if(symbol.type.id() == ID_struct)
      {
        id.print(std::cout);
        assert(id.is_scope);
        new_set.insert(&id);
      }
      #endif
    }
    else if(id.id_class==cpp_scopet::id_classt::TEMPLATE_PARAMETER)
    {
      // std::cout << "X4\n";
      // a template parameter may evaluate to be a scope: it could
      // be instantiated with a class/struct/union/enum
      exprt e=cpp_typecheck.template_map.lookup(id.identifier);

      #if 0
      cpp_typecheck.template_map.print(std::cout);
      std::cout << "S: " << cpp_typecheck.cpp_scopes.current_scope().identifier
                << '\n';
      std::cout << "P: "
                << cpp_typecheck.cpp_scopes.current_scope().get_parent()
                << '\n';
      std::cout << "I: " << id.identifier << '\n';
      std::cout << "E: " << e.pretty() << '\n';
      #endif

      if(e.id()!=ID_type)
        continue; // expressions are definitively not a scope

      if(e.type().id() == ID_template_parameter_symbol_type)
      {
        auto type = to_template_parameter_symbol_type(e.type());

        while(true)
        {
          irep_idt identifier=type.get_identifier();

          const symbolt &symbol=cpp_typecheck.lookup(identifier);
          assert(symbol.is_type);

          if(symbol.type.id() == ID_template_parameter_symbol_type)
            type = to_template_parameter_symbol_type(symbol.type);
          else if(symbol.type.id()==ID_struct ||
                  symbol.type.id()==ID_union ||
                  symbol.type.id()==ID_c_enum)
          {
            // this is a scope, too!
            cpp_idt &class_id=
              cpp_typecheck.cpp_scopes.get_id(identifier);

            assert(class_id.is_scope);
            new_set.insert(&class_id);
            break;
          }
          else // give up
            break;
        }
      }
    }
  }

  id_set.swap(new_set);
}

void cpp_typecheck_resolvet::filter_for_namespaces(
  cpp_scopest::id_sett &id_set)
{
  // we only want namespaces
  for(cpp_scopest::id_sett::iterator
      it=id_set.begin();
      it!=id_set.end();
      ) // no it++
  {
    if((*it)->is_namespace())
      it++;
    else
    {
      cpp_scopest::id_sett::iterator old(it);
      it++;
      id_set.erase(old);
    }
  }
}

void cpp_typecheck_resolvet::resolve_with_arguments(
  cpp_scopest::id_sett &id_set,
  const irep_idt &base_name,
  const cpp_typecheck_fargst &fargs)
{
  // not clear what this is good for
  for(const auto &arg : fargs.operands)
  {
    const typet &final_type=cpp_typecheck.follow(arg.type());

    if(final_type.id()!=ID_struct && final_type.id()!=ID_union)
      continue;

    cpp_scopet &scope=
      cpp_typecheck.cpp_scopes.get_scope(final_type.get(ID_name));
    const auto tmp_set = scope.lookup(base_name, cpp_scopet::SCOPE_ONLY);
    id_set.insert(tmp_set.begin(), tmp_set.end());
  }
}

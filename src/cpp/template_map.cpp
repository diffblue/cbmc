/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "template_map.h"

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include "cpp_template_parameter.h"
#include "cpp_template_type.h"

#include <ostream>

void template_mapt::apply(typet &type) const
{
  if(type.id()==ID_array)
  {
    // C++26 pack indexing: Ts...[N] is parsed as array[N](Ts).
    // Before applying substitution, check if the element type is a
    // cpp_name matching a pack parameter and the size is a constant.
    if(
      to_array_type(type).element_type().id() == ID_cpp_name &&
      to_array_type(type).size().id() == ID_constant)
    {
      const auto &elem = to_array_type(type).element_type();
      const auto &sub = elem.get_sub();
      if(!sub.empty() && sub.front().id() == ID_name)
      {
        irep_idt base = sub.front().get(ID_identifier);
        for(const auto &entry : pack_args_map)
        {
          const std::string &key = id2string(entry.first);
          auto pos = key.rfind("::");
          std::string suffix =
            pos != std::string::npos ? key.substr(pos + 2) : key;
          if(suffix == id2string(base))
          {
            const auto &pack_types = entry.second;
            auto idx = numeric_cast_v<mp_integer>(
              to_constant_expr(to_array_type(type).size()));
            if(idx >= 0 && idx < pack_types.size())
            {
              type = pack_types[numeric_cast_v<std::size_t>(idx)];
              return;
            }
          }
        }
      }
    }
    apply(to_array_type(type).element_type());
    apply(to_array_type(type).size());
  }
  else if(type.id()==ID_pointer)
  {
    apply(to_pointer_type(type).base_type());
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    for(auto &c : to_struct_union_type(type).components())
    {
      typet &subtype = c.type();
      apply(subtype);
    }

    // also apply to base classes
    if(type.id() == ID_struct)
    {
      irept::subt &bases = type.add(ID_bases).get_sub();
      for(auto &base : bases)
        apply(static_cast<typet &>(base.add(ID_type)));
    }
  }
  else if(type.id() == ID_template_parameter_symbol_type)
  {
    type_mapt::const_iterator m_it =
      type_map.find(to_template_parameter_symbol_type(type).get_identifier());

    if(m_it!=type_map.end())
    {
      type=m_it->second;
      return;
    }
  }
  else if(type.id()==ID_code)
  {
    apply(to_code_type(type).return_type());

    irept::subt &parameters=type.add(ID_parameters).get_sub();

    for(auto &parameter : parameters)
    {
      if(parameter.id() == ID_parameter)
        apply(static_cast<typet &>(parameter.add(ID_type)));
    }
  }
  else if(type.id() == ID_function_type)
  {
    // Pre-conversion function type: apply to return type subtype
    // and to parameter declaration types.
    if(type.has_subtypes())
    {
      for(auto &st : to_type_with_subtypes(type).subtypes())
        apply(st);
    }
    irept::subt &parameters = type.add(ID_parameters).get_sub();
    for(auto &parameter : parameters)
    {
      if(parameter.id() == ID_cpp_declaration)
        apply(static_cast<typet &>(parameter.add(ID_type)));
    }
  }
  else if(type.id()==ID_merged_type)
  {
    for(typet &subtype : to_type_with_subtypes(type).subtypes())
      apply(subtype);
  }
  else if(type.id() == ID_cpp_name)
  {
    // Check if the cpp_name is a simple template type parameter
    irept::subt &sub = type.get_sub();
    if(!sub.empty() && sub.front().id() == ID_name)
    {
      irep_idt base = sub.front().get(ID_identifier);

      // Check for template template parameter usage like C<T>
      bool has_targs = false;
      for(const auto &s : sub)
        if(s.id() == ID_template_args)
          has_targs = true;

      // Try to match against type_map entries
      for(const auto &entry : type_map)
      {
        const std::string &key = id2string(entry.first);
        auto pos = key.rfind("::");
        std::string suffix =
          pos != std::string::npos ? key.substr(pos + 2) : key;
        if(
          suffix == id2string(base) && entry.second.id() != ID_unassigned &&
          entry.second.id() != ID_nil)
        {
          if(has_targs || sub.size() == 1)
          {
            type = entry.second;
            return;
          }
          // Qualified name like _Up::X where _Up maps to a struct:
          // replace _Up with the struct's base name so scope
          // resolution can find the member.
          if(sub.size() > 1 && entry.second.id() == ID_struct_tag)
          {
            irep_idt tag = to_struct_tag_type(entry.second).get_identifier();
            std::string tag_str = id2string(tag);
            if(tag_str.substr(0, 4) == "tag-")
              tag_str = tag_str.substr(4);
            sub.front() = irept{ID_name};
            sub.front().set(ID_identifier, tag_str);
            return;
          }
        }
      }
    }

    // apply to template arguments within cpp_name
    for(auto &s : sub)
    {
      if(s.id() == ID_template_args)
      {
        irept::subt &args = s.add(ID_arguments).get_sub();
        for(auto &arg : args)
          apply(static_cast<exprt &>(arg));
      }
    }
  }
}

void template_mapt::apply(exprt &expr) const
{
  apply(expr.type());

  // Recursively apply to ALL named sub-nodes to handle deeply
  // nested template parameters (e.g., inside decltype expressions).
  for(auto &named : expr.get_named_sub())
  {
    if(named.first == irep_idt{"operands"} || named.first == "#source_location")
      continue; // handled separately or not relevant
    if(named.second.id() == ID_nil)
      continue;
    apply(static_cast<typet &>(named.second));
  }

  // Also apply to all sub-nodes (the unnamed children)
  for(auto &sub : expr.get_sub())
    apply(static_cast<typet &>(sub));

  // Handle sizeof...(Pack) — replace with pack size constant
  if(expr.id() == ID_sizeof)
  {
    irept &type_arg = expr.add(ID_type_arg);
    if(type_arg.is_not_nil())
      apply(static_cast<typet &>(type_arg));
  }

  // Apply to type predicate arguments (type_arg, type_arg1, type_arg2)
  if(expr.find(ID_type_arg).is_not_nil() && expr.id() != ID_sizeof)
    apply(static_cast<typet &>(expr.add(ID_type_arg)));
  if(expr.find("type_arg1").is_not_nil())
    apply(static_cast<typet &>(expr.add("type_arg1")));
  if(expr.find("type_arg2").is_not_nil())
    apply(static_cast<typet &>(expr.add("type_arg2")));

  if(expr.id()==ID_symbol)
  {
    expr_mapt::const_iterator m_it =
      expr_map.find(to_symbol_expr(expr).get_identifier());

    if(m_it!=expr_map.end())
    {
      expr=m_it->second;
      return;
    }
  }

  // Substitute non-type template parameters inside cpp_name
  // template arguments. These appear as "ambiguous" nodes with
  // a type containing a cpp_name whose identifier matches an
  // expr_map entry (e.g., _Num in __static_abs<_Num>::value).
  std::function<void(irept &)> subst_params = [&](irept &node)
  {
    if(node.id() == ID_template_args)
    {
      irept &args = node.add(ID_arguments);
      for(auto &arg : args.get_sub())
      {
        if(arg.id() != ID_ambiguous)
          continue;
        // The ambiguous node stores the cpp_name in its "type" field
        const irept &inner = arg.find(ID_type);
        if(inner.id() != ID_cpp_name)
          continue;
        // Check if the cpp_name is a single identifier
        if(inner.get_sub().size() != 1 || inner.get_sub()[0].id() != ID_name)
          continue;
        const std::string target =
          id2string(inner.get_sub()[0].get(ID_identifier));
        for(const auto &entry : expr_map)
        {
          const std::string &key = id2string(entry.first);
          if(
            key == target ||
            (key.size() > target.size() + 2 &&
             key.substr(key.size() - target.size()) == target &&
             key[key.size() - target.size() - 1] == ':'))
          {
            arg = entry.second;
            break;
          }
        }
      }
    }
    for(auto &sub : node.get_sub())
      subst_params(sub);
    for(auto &named : node.get_named_sub())
      subst_params(named.second);
  };
  subst_params(expr);
}

exprt template_mapt::lookup(const irep_idt &identifier) const
{
  type_mapt::const_iterator t_it=
    type_map.find(identifier);

  if(t_it!=type_map.end())
  {
    exprt e(ID_type);
    e.type()=t_it->second;
    return e;
  }

  expr_mapt::const_iterator e_it=
    expr_map.find(identifier);

  if(e_it!=expr_map.end())
    return e_it->second;

  return static_cast<const exprt &>(get_nil_irep());
}

typet template_mapt::lookup_type(const irep_idt &identifier) const
{
  type_mapt::const_iterator t_it=
    type_map.find(identifier);

  if(t_it!=type_map.end())
    return t_it->second;

  return static_cast<const typet &>(get_nil_irep());
}

exprt template_mapt::lookup_expr(const irep_idt &identifier) const
{
  expr_mapt::const_iterator e_it=
    expr_map.find(identifier);

  if(e_it!=expr_map.end())
    return e_it->second;

  return static_cast<const exprt &>(get_nil_irep());
}

exprt template_mapt::lookup_by_suffix(const std::string &suffix) const
{
  const std::string match = "::" + suffix;
  for(const auto &entry : type_map)
  {
    const std::string key = id2string(entry.first);
    if(
      key.size() >= match.size() &&
      key.compare(key.size() - match.size(), match.size(), match) == 0)
    {
      exprt e(ID_type);
      e.type() = entry.second;
      return e;
    }
  }
  for(const auto &entry : expr_map)
  {
    const std::string key = id2string(entry.first);
    if(
      key.size() >= match.size() &&
      key.compare(key.size() - match.size(), match.size(), match) == 0)
    {
      return entry.second;
    }
  }
  return static_cast<const exprt &>(get_nil_irep());
}

void template_mapt::print(std::ostream &out) const
{
  for(const auto &mapping : type_map)
    out << mapping.first << " = " << mapping.second.pretty() << '\n';

  for(const auto &mapping : expr_map)
    out << mapping.first << " = " << mapping.second.pretty() << '\n';
}

void template_mapt::build(
  const template_typet &template_type,
  const cpp_template_args_tct &template_args)
{
  const template_typet::template_parameterst &template_parameters=
    template_type.template_parameters();

  cpp_template_args_tct::argumentst instance=
    template_args.arguments();

  if(instance.size()<template_parameters.size())
  {
    // check for default parameters
    for(std::size_t i=instance.size();
        i<template_parameters.size();
        i++)
    {
      const template_parametert &param=template_parameters[i];

      if(param.has_default_argument())
        instance.push_back(param.default_argument());
      else
        break;
    }
  }

  // these should have been typechecked before
  bool has_pack = !template_parameters.empty() &&
                  template_parameters.back().get_bool(ID_ellipsis);
  if(
    instance.size() != template_parameters.size() &&
    !(has_pack && instance.size() >= template_parameters.size() - 1))
  {
    return; // mismatched template arguments — skip
  }

  std::size_t i = 0;
  for(cpp_template_args_tct::argumentst::const_iterator i_it = instance.begin();
      i_it != instance.end();
      i_it++, i++)
  {
    if(i < template_parameters.size())
    {
      set(template_parameters[i], *i_it);
    }
    // Extra arguments for variadic packs are not mapped to individual
    // parameters; they are passed through in the template args.
  }

  // Record pack sizes for sizeof...(Pack)
  if(has_pack)
  {
    const auto &pack_param = template_parameters.back();
    irep_idt pack_id = pack_param.id() == ID_type
                         ? pack_param.type().get(ID_identifier)
                         : pack_param.get(ID_identifier);
    std::size_t non_pack = template_parameters.size() - 1;
    std::size_t pack_sz =
      instance.size() >= non_pack ? instance.size() - non_pack : 0;
    pack_size_map[pack_id] = pack_sz;

    // Store all pack argument types for pack indexing (C++26)
    std::vector<typet> pack_types;
    for(std::size_t j = non_pack; j < instance.size(); ++j)
    {
      if(instance[j].id() == ID_type)
        pack_types.push_back(instance[j].type());
    }
    if(!pack_types.empty())
      pack_args_map[pack_id] = std::move(pack_types);
  }
}

void template_mapt::set(
  const template_parametert &parameter,
  const exprt &value)
{
  if(parameter.id()==ID_type)
  {
    if(parameter.id()!=ID_type)
      UNREACHABLE; // typechecked before!

    typet tmp=value.type();

    irep_idt identifier=parameter.type().get(ID_identifier);
    type_map[identifier]=tmp;
  }
  else
  {
    // must be non-type

    if(value.id()==ID_type)
      UNREACHABLE; // typechecked before!

    irep_idt identifier=parameter.get(ID_identifier);
    expr_map[identifier]=value;
  }
}

void template_mapt::build_unassigned(
  const template_typet &template_type)
{
  for(const auto &t : template_type.template_parameters())
  {
    if(t.id()==ID_type)
    {
      typet tmp(ID_unassigned);
      tmp.set(ID_identifier, t.type().get(ID_identifier));
      tmp.add_source_location()=t.source_location();
      type_map[t.type().get(ID_identifier)]=tmp;
    }
    else
    {
      exprt tmp(ID_unassigned, t.type());
      tmp.set(ID_identifier, t.get(ID_identifier));
      tmp.add_source_location()=t.source_location();
      expr_map[t.get(ID_identifier)]=tmp;
    }
  }
}

cpp_template_args_tct template_mapt::build_template_args(
  const template_typet &template_type) const
{
  const template_typet::template_parameterst &template_parameters=
    template_type.template_parameters();

  cpp_template_args_tct template_args;
  template_args.arguments().resize(template_parameters.size());

  for(std::size_t i=0; i<template_parameters.size(); i++)
  {
    const template_parametert &t=template_parameters[i];

    if(t.id()==ID_type)
    {
      template_args.arguments()[i]=
        exprt(ID_type, lookup_type(t.type().get(ID_identifier)));
    }
    else
    {
      template_args.arguments()[i]=
        lookup_expr(t.get(ID_identifier));
    }
  }

  return template_args;
}

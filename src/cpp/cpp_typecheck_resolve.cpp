/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck_resolve.h"

#ifdef DEBUG
#  include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

extern exprt try_evaluate_constexpr(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns);
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include <ansi-c/anonymous_member.h>
#include <ansi-c/merged_type.h>

#include "cpp_convert_type.h"
#include "cpp_template_parameter.h"
#include "cpp_template_qualifiers.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"

#include <algorithm>
#include <set>

cpp_typecheck_resolvet::cpp_typecheck_resolvet(cpp_typecheckt &_cpp_typecheck)
  : cpp_typecheck(_cpp_typecheck),
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
    exprt e = convert_identifier(identifier, fargs);

    if(e.is_not_nil())
    {
      CHECK_RETURN(e.id() != ID_type || e.type().is_not_nil());

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
      CHECK_RETURN(e.id() != ID_type || e.type().is_not_nil());

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

  resolve_identifierst non_templates;

  // C++20 concept subsumption: when multiple templates with concept
  // constraints match, prefer the more constrained one. Filter before
  // instantiation so only the best candidate is instantiated.
  if(old_identifiers.size() > 1)
  {
    // Extract concept constraint from template parameters
    auto get_constraint = [&](const exprt &id) -> irep_idt
    {
      const typet &t =
        id.type().id() == ID_struct_tag
          ? static_cast<const typet &>(
              cpp_typecheck.follow_tag(to_struct_tag_type(id.type())))
        : id.type().id() == ID_union_tag
          ? static_cast<const typet &>(
              cpp_typecheck.follow_tag(to_union_tag_type(id.type())))
          : id.type();
      if(!t.get_bool(ID_is_template))
        return irep_idt();
      const cpp_declarationt &decl = to_cpp_declaration(t);
      for(const auto &p : decl.template_type().template_parameters())
      {
        const irep_idt &c = p.get("#C_concept_constraint");
        if(!c.empty())
          return c;
      }
      return irep_idt();
    };

    std::vector<bool> subsumed(old_identifiers.size(), false);
    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      irep_idt ci = get_constraint(old_identifiers[i]);
      if(ci.empty())
        continue;
      for(std::size_t j = 0; j < old_identifiers.size(); ++j)
      {
        if(i == j)
          continue;
        irep_idt cj = get_constraint(old_identifiers[j]);
        if(cj.empty())
          continue;
        if(id2string(cj).find(id2string(ci)) != std::string::npos && ci != cj)
        {
          subsumed[i] = true;
        }
      }
    }

    bool any_subsumed = false;
    for(bool s : subsumed)
      if(s)
        any_subsumed = true;

    if(any_subsumed)
    {
      resolve_identifierst filtered;
      for(std::size_t i = 0; i < old_identifiers.size(); ++i)
        if(!subsumed[i])
          filtered.push_back(old_identifiers[i]);
      old_identifiers.swap(filtered);
    }
  }

  for(const auto &old_id : old_identifiers)
  {
    exprt e = guess_function_template_args(old_id, fargs);

    if(e.is_not_nil())
    {
      CHECK_RETURN(e.id() != ID_type);

      // C++20: check concept constraint satisfaction
      bool concept_ok = true;
      {
        irep_idt tmpl_id = old_id.get(ID_identifier);
        if(tmpl_id.empty() && old_id.id() == ID_symbol)
          tmpl_id = to_symbol_expr(old_id).get_identifier();
        const auto *tmpl_sym = cpp_typecheck.symbol_table.lookup(tmpl_id);
        if(tmpl_sym && tmpl_sym->type.get_bool(ID_is_template))
        {
          const cpp_declarationt &tdecl = to_cpp_declaration(tmpl_sym->type);
          for(const auto &p : tdecl.template_type().template_parameters())
          {
            const irep_idt &cc = p.get("#C_concept_constraint");
            if(cc.empty())
              continue;
            // Get the deduced type from fargs
            typet actual_type;
            if(!fargs.operands.empty())
              actual_type = fargs.operands[0].type();
            if(actual_type.is_nil())
              break;
            // Look up concept definition
            for(const auto &entry : cpp_typecheck.symbol_table)
            {
              if(
                id2string(entry.second.base_name) != id2string(cc) ||
                !entry.second.type.get_bool(ID_is_template))
                continue;
              const cpp_declarationt &concept_decl =
                to_cpp_declaration(entry.second.type);
              if(concept_decl.declarators().empty())
                break;
              const exprt &cval = concept_decl.declarators()[0].value();
              if(cval.is_nil())
                break;
              // Get concept parameter name
              irep_idt cparam;
              for(const auto &cp :
                  concept_decl.template_type().template_parameters())
              {
                if(cp.id() == ID_type)
                {
                  const std::string cid =
                    id2string(cp.type().get(ID_identifier));
                  auto pos = cid.rfind("::");
                  cparam = pos != std::string::npos
                             ? irep_idt{cid.substr(pos + 2)}
                             : irep_idt{cid};
                  break;
                }
              }
              if(cparam.empty())
                break;
              // Evaluate the concept definition with the actual type.
              // Resolve a type from a cpp_name node.
              auto resolve_type = [&](const irept &node) -> typet
              {
                if(node.id() == ID_cpp_name)
                {
                  for(const auto &s : node.get_sub())
                    if(s.id() == ID_name && s.get(ID_identifier) == cparam)
                      return actual_type;
                }
                return typet{};
              };

              // Evaluate an expression tree directly.
              std::function<int(const irept &)> eval =
                [&](const irept &node) -> int
              {
                // -1 = unknown, 0 = false, 1 = true
                if(node.id() == ID_and)
                {
                  for(const auto &sub : node.get_sub())
                  {
                    int v = eval(sub);
                    if(v == 0)
                      return 0;
                    if(v == -1)
                      return -1;
                  }
                  return 1;
                }
                if(node.id() == ID_or)
                {
                  bool any_unknown = false;
                  for(const auto &sub : node.get_sub())
                  {
                    int v = eval(sub);
                    if(v == 1)
                      return 1;
                    if(v == -1)
                      any_unknown = true;
                  }
                  return any_unknown ? -1 : 0;
                }
                if(node.id() == ID_not)
                {
                  if(node.get_sub().empty())
                    return -1;
                  int v = eval(node.get_sub()[0]);
                  return v == -1 ? -1 : (v ? 0 : 1);
                }
                // sizeof(T) <= N
                if(
                  node.id() == ID_le || node.id() == ID_lt ||
                  node.id() == ID_ge || node.id() == ID_gt)
                {
                  // Try to evaluate via typecheck+simplify
                  exprt cmp = static_cast<const exprt &>(node);
                  std::function<void(irept &)> subst_types = [&](irept &n)
                  {
                    if(n.id() == ID_cpp_name)
                    {
                      for(const auto &s : n.get_sub())
                        if(s.id() == ID_name && s.get(ID_identifier) == cparam)
                        {
                          n = actual_type;
                          return;
                        }
                    }
                    for(auto &sub : n.get_sub())
                      subst_types(sub);
                    for(auto &named : n.get_named_sub())
                      subst_types(named.second);
                  };
                  subst_types(cmp);
                  try
                  {
                    cpp_typecheck.typecheck_expr(cmp);
                    simplify(cmp, cpp_typecheck);
                    if(cmp.is_true())
                      return 1;
                    if(cmp.is_false())
                      return 0;
                  }
                  catch(...)
                  {
                  }
                  return -1;
                }
                // Type trait: side_effect(function_call)
                if(node.id() == ID_side_effect)
                {
                  const auto &subs = node.get_sub();
                  if(subs.size() >= 2 && subs[0].id() == ID_cpp_name)
                  {
                    irep_idt fname;
                    for(const auto &s : subs[0].get_sub())
                      if(s.id() == ID_name)
                        fname = s.get(ID_identifier);
                    const auto &args = subs[1].get_sub();
                    if(args.empty())
                      return -1;
                    typet arg_type = resolve_type(args[0]);
                    if(arg_type.is_nil())
                      return -1;
                    if(fname == "__is_integral")
                      return (arg_type.id() == ID_signedbv ||
                              arg_type.id() == ID_unsignedbv ||
                              arg_type.id() == ID_bool ||
                              arg_type.id() == ID_c_bool)
                               ? 1
                               : 0;
                    if(fname == "__is_floating_point")
                      return (arg_type.id() == ID_floatbv ||
                              arg_type.id() == ID_fixedbv)
                               ? 1
                               : 0;
                    if(fname == "__is_pointer")
                      return arg_type.id() == ID_pointer ? 1 : 0;
                    if(fname == "__is_signed")
                      return arg_type.id() == ID_signedbv ? 1 : 0;
                    if(fname == "__is_same")
                    {
                      if(args.size() >= 2)
                      {
                        typet t2 = resolve_type(args[1]);
                        if(!t2.is_nil())
                          return arg_type == t2 ? 1 : 0;
                      }
                      return -1;
                    }
                  }
                }
                // compound requirement: check method return type
                if(node.id() == irep_idt{"compound_requirement"})
                {
                  const irep_idt &method =
                    static_cast<const exprt &>(node).get("#method");
                  const auto &constraint = node.find("#constraint");
                  if(method.empty() || constraint.is_nil())
                    return -1;
                  if(actual_type.id() != ID_struct_tag)
                    return -1;
                  const auto &struct_type = to_struct_type(
                    cpp_typecheck.follow_tag(to_struct_tag_type(actual_type)));
                  typet return_type;
                  for(const auto &comp : struct_type.components())
                  {
                    if(
                      comp.get_base_name() == method &&
                      comp.type().id() == ID_code)
                    {
                      return_type = to_code_type(comp.type()).return_type();
                      break;
                    }
                  }
                  if(return_type.is_nil())
                    return -1;
                  // Extract expected type from constraint template args.
                  // Structure: cpp_name(name, template_args(arguments=(...)))
                  // The arguments named sub contains nodes with type subs.
                  typet expected_type;
                  for(const auto &sub : constraint.get_sub())
                  {
                    if(sub.id() == ID_template_args)
                    {
                      const auto &args = sub.find(ID_arguments);
                      if(!args.is_nil())
                      {
                        for(const auto &arg : args.get_sub())
                        {
                          const auto &t = arg.find(ID_type);
                          if(!t.is_nil())
                          {
                            expected_type = static_cast<const typet &>(t);
                            break;
                          }
                        }
                      }
                      break;
                    }
                  }
                  if(expected_type.is_nil())
                    return -1;
                  try
                  {
                    cpp_typecheck.typecheck_type(expected_type);
                  }
                  catch(...)
                  {
                    return -1;
                  }
                  return return_type == expected_type ? 1 : 0;
                }
                // typecast(true) — from requires-expression fallback
                if(node.id() == ID_typecast)
                {
                  const auto &subs = node.get_sub();
                  if(!subs.empty())
                    return eval(subs[0]);
                }
                if(node.id() == ID_constant)
                {
                  const auto &val = static_cast<const exprt &>(node);
                  if(val.is_true())
                    return 1;
                  if(val.is_false())
                    return 0;
                }
                return -1;
              };

              int result = eval(cval);
              if(result == 0)
                concept_ok = false;
              break;
            }
            break;
          }
        }
      }

      if(concept_ok)
        identifiers.push_back(e);
    }
    else if(old_id.id() == ID_symbol)
    {
      const irep_idt &sym_name = to_symbol_expr(old_id).get_identifier();
      auto alt_it = cpp_typecheck.sfinae_alternatives.find(sym_name);
      if(alt_it != cpp_typecheck.sfinae_alternatives.end())
      {
        // Primary overload failed SFINAE — try the alternative.
        const irep_idt &alt_name = id2string(sym_name) + "#sfinae_alt";
        if(!cpp_typecheck.symbol_table.has_symbol(alt_name))
          cpp_typecheck.symbol_table.insert(alt_it->second);
        exprt alt_id = old_id;
        alt_id.type() = alt_it->second.type;
        to_symbol_expr(alt_id).set_identifier(alt_name);
        exprt alt_e = guess_function_template_args(alt_id, fargs);
        if(alt_e.is_not_nil())
        {
          CHECK_RETURN(alt_e.id() != ID_type);
          identifiers.push_back(alt_e);
        }
      }
      else if(!old_id.type().get_bool(ID_is_template))
      {
        non_templates.push_back(old_id);
      }
    }
  }

  // Only include non-template identifiers when there are also template
  // function instances — they need to participate in disambiguation.
  // When there are no template instances, leave identifiers empty so
  // the caller falls back to the non-template resolution path.
  if(!identifiers.empty())
  {
    for(auto &nt : non_templates)
      identifiers.push_back(std::move(nt));
  }

  disambiguate_functions(identifiers, fargs);

  // there should only be one left, or we have failed to disambiguate
  if(identifiers.size() == 1)
  {
    exprt e = *identifiers.begin();

    // If a non-template identifier won disambiguation, keep it as-is.
    if(e.id() != ID_template_function_instance)
      return;

    // instantiate that one
    CHECK_RETURN(e.id() == ID_template_function_instance);

    const symbolt &template_symbol =
      cpp_typecheck.lookup(e.type().get(ID_C_template));

    const cpp_template_args_tct &template_args =
      to_cpp_template_args_tc(e.type().find(ID_C_template_arguments));

    // Let's build the instance.

    // For template constructors in instantiated template classes,
    // pre-populate the template map with the class template arguments.
    cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);
    const irep_idt &inst_class_tag = e.type().get(ID_C_class);
    if(!inst_class_tag.empty())
    {
      const symbolt *class_sym =
        cpp_typecheck.symbol_table.lookup(inst_class_tag);
      if(
        class_sym != nullptr &&
        class_sym->type.find(ID_C_template).is_not_nil() &&
        class_sym->type.find(ID_C_template_arguments).is_not_nil())
      {
        cpp_typecheck.template_map.build(
          static_cast<const template_typet &>(
            class_sym->type.find(ID_C_template)),
          static_cast<const cpp_template_args_tct &>(
            class_sym->type.find(ID_C_template_arguments)));
      }
    }

    const symbolt &new_symbol = cpp_typecheck.instantiate_template(
      source_location, template_symbol, template_args, template_args);

    identifiers.clear();
    // The instantiated function may have function pointer parameters
    // with spurious ellipsis from variadic template pack expansion.
    // Check and fix the type before returning.
    typet inst_type = new_symbol.type;
    if(inst_type.id() == ID_code)
    {
      bool has_variadic_pack = false;
      const cpp_declarationt &tmpl_decl =
        to_cpp_declaration(template_symbol.type);
      for(const auto &p : tmpl_decl.template_type().template_parameters())
      {
        if(p.get_bool(ID_ellipsis))
        {
          has_variadic_pack = true;
          break;
        }
      }

      if(has_variadic_pack)
      {
        for(auto &param : to_code_type(inst_type).parameters())
        {
          if(param.type().id() == ID_pointer)
          {
            typet &base = to_pointer_type(param.type()).base_type();
            if(base.id() == ID_code)
            {
              code_typet &ct = to_code_type(base);
              if(ct.has_ellipsis())
                ct.remove_ellipsis();
            }
          }
        }

        // Expand pack parameter: the instantiated function has a single
        // parameter for the pack, but it should have N copies where N
        // is the pack size (extra template args beyond non-pack params).
        const auto &tmpl_params =
          tmpl_decl.template_type().template_parameters();
        std::size_t non_pack_count = 0;
        for(const auto &tp : tmpl_params)
        {
          if(!tp.get_bool(ID_ellipsis))
            ++non_pack_count;
        }
        std::size_t pack_size =
          template_args.arguments().size() > non_pack_count
            ? template_args.arguments().size() - non_pack_count
            : 0;

        if(pack_size > 1)
        {
          auto &params = to_code_type(inst_type).parameters();
          // Find the pack parameter (last one that was the pack)
          // and duplicate it to match the pack size.
          // The pack parameter is at position non_pack_count in the
          // function parameters (after 'this' if present).
          std::size_t param_offset = 0;
          if(!params.empty() && params.front().get_this())
            param_offset = 1;

          // Only expand if the parameter count doesn't already match
          // (instantiate_template may have already expanded the pack).
          std::size_t expected_params =
            non_pack_count + pack_size + param_offset;
          if(
            params.size() < expected_params &&
            non_pack_count + param_offset < params.size())
          {
            std::size_t pack_idx = non_pack_count + param_offset;
            code_typet::parametert pack_param = params[pack_idx];
            for(std::size_t i = 1; i < pack_size; ++i)
              params.insert(params.begin() + pack_idx + i, pack_param);
          }
        }
      }
    }

    identifiers.push_back(symbol_exprt(new_symbol.name, inst_type));
  }
}

void cpp_typecheck_resolvet::remove_templates(resolve_identifierst &identifiers)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    const typet &followed =
      old_id.type().id() == ID_struct_tag
        ? static_cast<const typet &>(
            cpp_typecheck.follow_tag(to_struct_tag_type(old_id.type())))
      : old_id.type().id() == ID_union_tag
        ? static_cast<const typet &>(
            cpp_typecheck.follow_tag(to_union_tag_type(old_id.type())))
      : old_id.type().id() == ID_c_enum_tag
        ? static_cast<const typet &>(
            cpp_typecheck.follow_tag(to_c_enum_tag_type(old_id.type())))
        : old_id.type();
    if(!followed.get_bool(ID_is_template))
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

    if(id.empty())
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
  std::cout << "RESOLVE MAP:\n";
  cpp_typecheck.template_map.print(std::cout);
#endif

  // look up the parameter in the template map
  exprt e = cpp_typecheck.template_map.lookup(identifier.identifier);

  // If not found, the parameter may have been registered under a different
  // template scope (e.g., forward declaration vs definition). Try matching
  // by base name.
  if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
  {
    const std::string id_str = id2string(identifier.identifier);
    auto pos = id_str.rfind("::");
    if(pos != std::string::npos)
    {
      const std::string base = id_str.substr(pos + 2);
      e = cpp_typecheck.template_map.lookup_by_suffix(base);
    }
  }

  if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
  {
    // Don't print an error message — the caller may catch the exception
    // (e.g., during SFINAE or template argument deduction).
    throw 0;
  }

  e.add_source_location() = source_location;

  return e;
}

exprt cpp_typecheck_resolvet::convert_identifier(
  const cpp_idt &identifier,
  const cpp_typecheck_fargst &fargs)
{
  if(identifier.id_class == cpp_scopet::id_classt::TEMPLATE_PARAMETER)
    return convert_template_parameter(identifier);

  exprt e;

  if(
    identifier.is_member && !identifier.is_constructor &&
    !identifier.is_static_member)
  {
    // a regular struct or union member

    const symbolt *compound_ptr =
      cpp_typecheck.symbol_table.lookup(identifier.class_identifier);
    if(!compound_ptr)
    {
      exprt nil;
      nil.make_nil();
      return nil;
    }
    const symbolt &compound_symbol = *compound_ptr;

    CHECK_RETURN(
      compound_symbol.type.id() == ID_struct ||
      compound_symbol.type.id() == ID_union);

    const struct_union_typet &struct_union_type =
      to_struct_union_type(compound_symbol.type);

    const exprt &component =
      struct_union_type.get_component(identifier.identifier);

    const typet &type = component.type();
    DATA_INVARIANT(type.is_not_nil(), "type must not be nil");

    if(identifier.id_class == cpp_scopet::id_classt::TYPEDEF)
    {
      e = type_exprt(type);
    }
    else if(identifier.id_class == cpp_scopet::id_classt::SYMBOL)
    {
      // A non-static, non-type member.
      // There has to be an object.
      e = exprt(ID_member);
      e.set(ID_component_name, identifier.identifier);
      e.add_source_location() = source_location;

      exprt object;
      object.make_nil();

#if 0
      std::cout << "I: " << identifier.class_identifier
                << " "
                << cpp_typecheck.cpp_scopes.current_scope().
                    this_class_identifier << '\n';
#endif

      const exprt &this_expr = original_scope->this_expr;

      if(fargs.has_object)
      {
        // the object is given to us in fargs
        PRECONDITION(!fargs.operands.empty());
        object = fargs.operands.front();
      }
      else if(this_expr.is_not_nil())
      {
        // use this->...
        DATA_INVARIANT(
          this_expr.type().id() == ID_pointer,
          "this argument should be pointer");
        object =
          exprt(ID_dereference, to_pointer_type(this_expr.type()).base_type());
        object.copy_to_operands(this_expr);
        object.type().set(
          ID_C_constant,
          to_pointer_type(this_expr.type())
            .base_type()
            .get_bool(ID_C_constant));
        object.set(ID_C_lvalue, true);
        object.add_source_location() = source_location;
      }

      // check if the member can be applied to the object
      if(
        (object.type().id() != ID_struct_tag &&
         object.type().id() != ID_union_tag) ||
        !has_component_rec(object.type(), identifier.identifier, cpp_typecheck))
      {
        // failed
        object.make_nil();
      }

      if(object.is_not_nil())
      {
        // we got an object
        e.add_to_operands(std::move(object));

        bool old_value = cpp_typecheck.disable_access_control;
        cpp_typecheck.disable_access_control = true;
        cpp_typecheck.typecheck_expr_member(e);
        cpp_typecheck.disable_access_control = old_value;
      }
      else if(
        compound_symbol.type.id() == ID_union &&
        compound_symbol.type.find(ID_C_unnamed_object).is_not_nil())
      {
        // Anonymous union member: access through the unnamed object
        // variable rather than through 'this'.
        const irep_idt &unnamed_obj =
          compound_symbol.type.get(ID_C_unnamed_object);
        const symbolt *anon_sym =
          cpp_typecheck.symbol_table.lookup(unnamed_obj);
        if(anon_sym == nullptr)
        {
          // Try with scope prefix
          for(cpp_scopet *s = &cpp_typecheck.cpp_scopes.current_scope();
              !s->is_root_scope();
              s = &s->get_parent())
          {
            anon_sym = cpp_typecheck.symbol_table.lookup(
              id2string(s->prefix) + id2string(unnamed_obj));
            if(anon_sym != nullptr)
              break;
          }
        }
        if(anon_sym != nullptr)
        {
          exprt anon_obj = anon_sym->symbol_expr();
          anon_obj.set(ID_C_lvalue, true);
          e.add_to_operands(std::move(anon_obj));
          e.type() = type;
          bool old_value = cpp_typecheck.disable_access_control;
          cpp_typecheck.disable_access_control = true;
          cpp_typecheck.typecheck_expr_member(e);
          cpp_typecheck.disable_access_control = old_value;
        }
        else
        {
          e.id(ID_ptrmember);
          tag_typet class_tag_type{ID_union_tag, identifier.class_identifier};
          e.copy_to_operands(exprt("cpp-this", pointer_type(class_tag_type)));
          e.type() = type;
        }
      }
      else
      {
        // this has to be a method or form a pointer-to-member expression
        if(identifier.is_method)
        {
          const symbolt *sym_ptr =
            cpp_typecheck.symbol_table.lookup(identifier.identifier);
          if(!sym_ptr)
          {
            e.make_nil();
          }
          else
          {
            e = cpp_symbol_expr(*sym_ptr);
          }
        }
        else
        {
          e.id(ID_ptrmember);
          tag_typet class_tag_type{
            compound_symbol.type.id() == ID_struct ? ID_struct_tag
                                                   : ID_union_tag,
            identifier.class_identifier};
          e.copy_to_operands(exprt("cpp-this", pointer_type(class_tag_type)));
          e.type() = type;
        }
      }
    }
  }
  else
  {
    const symbolt *sym_ptr =
      cpp_typecheck.symbol_table.lookup(identifier.identifier);
    if(!sym_ptr)
    {
      exprt nil;
      nil.make_nil();
      return nil;
    }
    const symbolt &symbol = *sym_ptr;

    if(symbol.is_type)
    {
      e.make_nil();

      if(symbol.is_macro) // includes typedefs
      {
        e = type_exprt(symbol.type);
        PRECONDITION(symbol.type.is_not_nil());
      }
      else if(symbol.type.id() == ID_c_enum)
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
      if(symbol.type.id() == ID_code)
      {
        // constexpr function
        e = cpp_symbol_expr(symbol);
      }
      else if(
        symbol.type.id() == ID_struct || symbol.type.id() == ID_struct_tag)
      {
        // constexpr struct variable: keep as symbol so it remains an
        // lvalue for member function calls (this pointer formation)
        e = cpp_symbol_expr(symbol);
      }
      else
      {
        e = symbol.value;
        if(e.is_nil())
          e = cpp_symbol_expr(symbol);
      }
    }
    else
    {
      e = cpp_symbol_expr(symbol);
    }
  }

  e.add_source_location() = source_location;

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
    bool match = false;

    switch(want)
    {
    case wantt::TYPE:
      match = (old_id.id() == ID_type);
      break;

    case wantt::VAR:
      match = (old_id.id() != ID_type);
      break;

    case wantt::BOTH:
      match = true;
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
      if(distance <= 0)
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
      std::size_t template_distance = 0;

      if(!old_id.type().get(ID_C_template).empty())
        template_distance = old_id.type()
                              .find(ID_C_template_arguments)
                              .find(ID_arguments)
                              .get_sub()
                              .size();

      // we give strong preference to functions that have
      // fewer template arguments
      std::size_t total_distance =
        // NOLINTNEXTLINE(whitespace/operators)
        1000 * template_distance + args_distance;

      distance_map.insert({total_distance, old_id});
    }
  }

  old_identifiers.clear();

  // put in the top ones
  if(!distance_map.empty())
  {
    auto range = distance_map.equal_range(distance_map.begin()->first);
    for(auto it = range.first; it != range.second; ++it)
      old_identifiers.push_back(it->second);
  }

  if(old_identifiers.size() > 1 && fargs.in_use)
  {
    // Try to further disambiguate by partial ordering: a candidate is
    // "dominated" if another candidate has at least as specific
    // parameter types (via derived-to-base subtyping) for every
    // parameter and strictly more specific for at least one.
    std::vector<bool> dominated(old_identifiers.size(), false);

    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      if(old_identifiers[i].type().id() != ID_code)
        continue;

      const code_typet &f1 = to_code_type(old_identifiers[i].type());

      for(std::size_t j = 0; j < old_identifiers.size(); ++j)
      {
        if(i == j || dominated[j])
          continue;

        if(old_identifiers[j].type().id() != ID_code)
          continue;

        const code_typet &f2 = to_code_type(old_identifiers[j].type());

        if(f1.parameters().size() != f2.parameters().size())
          continue;

        // Check if f2 is at least as specific as f1 (i.e., f2
        // dominates f1): for each parameter, f2's type must be the
        // same as or a subtype (more derived) of f1's type.
        bool f2_at_least_as_specific = true;
        bool f2_strictly_more_specific = false;

        for(std::size_t p = 0;
            p < f1.parameters().size() && f2_at_least_as_specific;
            ++p)
        {
          typet type1 = f1.parameters()[p].type();
          typet type2 = f2.parameters()[p].type();

          if(type1 == type2)
            continue;

          if(is_reference(type1) != is_reference(type2))
          {
            f2_at_least_as_specific = false;
            continue;
          }

          if(type1.id() == ID_pointer)
            type1 = to_pointer_type(type1).base_type();
          if(type2.id() == ID_pointer)
            type2 = to_pointer_type(type2).base_type();

          if(type1.id() != ID_struct_tag || type2.id() != ID_struct_tag)
          {
            f2_at_least_as_specific = false;
            continue;
          }

          // f2's param type is a subtype (more derived) of f1's
          if(cpp_typecheck.subtype_typecast(
               cpp_typecheck.follow_tag(to_struct_tag_type(type2)),
               cpp_typecheck.follow_tag(to_struct_tag_type(type1))))
          {
            f2_strictly_more_specific = true;
          }
          else
          {
            f2_at_least_as_specific = false;
          }
        }

        if(f2_at_least_as_specific && f2_strictly_more_specific)
          dominated[i] = true;
      }
    }

    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      if(!dominated[i])
        identifiers.push_back(old_identifiers[i]);
    }
  }
  else
  {
    identifiers.swap(old_identifiers);
  }

  remove_duplicates(identifiers);
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

    // is it a POD?

    if(cpp_typecheck.cpp_is_pod(identifier.type()))
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
      if(identifier.type().id() == ID_c_enum_tag)
      {
        const code_typet t3(
          {code_typet::parametert(signed_int_type())}, identifier.type());
        exprt pod_constructor3(ID_pod_constructor, t3);
        new_identifiers.push_back(pod_constructor3);
      }
    }
    else if(identifier.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        cpp_typecheck.follow_tag(to_struct_tag_type(identifier.type()));

      // Collect identifiers already present to avoid duplicates
      std::set<irep_idt> existing_ids;
      for(const auto &existing : new_identifiers)
      {
        if(existing.id() == ID_symbol)
          existing_ids.insert(to_symbol_expr(existing).get_identifier());
      }

      // go over components
      for(const auto &component : struct_type.components())
      {
        const typet &type = component.type();

        if(component.get_bool(ID_from_base))
          continue;

        if(
          type.id() == ID_code &&
          to_code_type(type).return_type().id() == ID_constructor)
        {
          if(existing_ids.count(component.get_name()))
            continue;
          const symbolt &symb = cpp_typecheck.lookup(component.get_name());
          exprt e = cpp_symbol_expr(symb);
          e.type() = type;
          new_identifiers.push_back(e);
        }
      }

      // Also look for template constructors in the class scope.
      // Template constructors are not struct components; they are
      // stored as TEMPLATE entries in the class scope.
      const irep_idt &class_name = struct_type.get(ID_name);
      auto scope_it = cpp_typecheck.cpp_scopes.id_map.find(class_name);
      if(scope_it != cpp_typecheck.cpp_scopes.id_map.end())
      {
        cpp_scopet &class_scope = static_cast<cpp_scopet &>(*scope_it->second);
        const irep_idt &ctor_base_name =
          cpp_typecheck.lookup(class_name).base_name;
        cpp_scopet::id_sett tmpl_set = class_scope.lookup(
          ctor_base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);
        for(const auto &id_ptr : tmpl_set)
        {
          // Skip if already present (e.g., from convert_identifiers)
          bool already_present = false;
          for(const auto &existing : new_identifiers)
          {
            if(
              existing.id() == ID_symbol &&
              to_symbol_expr(existing).get_identifier() == id_ptr->identifier)
            {
              already_present = true;
              break;
            }
          }
          if(already_present)
            continue;

          const symbolt &symb = cpp_typecheck.lookup(id_ptr->identifier);
          exprt e = cpp_symbol_expr(symb);
          // Store the class tag so that template argument deduction
          // can pre-populate the template map with class template args.
          e.set(ID_C_class, class_name);
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

  const cpp_template_args_non_tct::argumentst &arguments =
    template_args.arguments();

  if(base_name == ID_unsignedbv || base_name == ID_signedbv)
  {
    if(arguments.size() != 1)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects one template argument, but got "
        << arguments.size() << messaget::eom;
      throw 0;
    }

    exprt argument = arguments.front(); // copy

    if(argument.id() == ID_type)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects one integer template argument, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    resolve_argument(argument, fargs);

    const auto i = numeric_cast<mp_integer>(argument);
    if(!i.has_value())
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << "template argument must be constant" << messaget::eom;
      throw 0;
    }

    if(*i < 1)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << "template argument must be greater than zero" << messaget::eom;
      throw 0;
    }

    dest = type_exprt(typet(base_name));
    dest.type().set(ID_width, integer2string(*i));
  }
  else if(base_name == ID_fixedbv)
  {
    if(arguments.size() != 2)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects two template arguments, but got "
        << arguments.size() << messaget::eom;
      throw 0;
    }

    exprt argument0 = arguments[0];
    resolve_argument(argument0, fargs);
    exprt argument1 = arguments[1];
    resolve_argument(argument1, fargs);

    if(argument0.id() == ID_type)
    {
      cpp_typecheck.error().source_location = argument0.find_source_location();
      cpp_typecheck.error()
        << base_name << " expects two integer template arguments, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    if(argument1.id() == ID_type)
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << base_name << " expects two integer template arguments, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    const auto width = numeric_cast<mp_integer>(argument0);

    if(!width.has_value())
    {
      cpp_typecheck.error().source_location = argument0.find_source_location();
      cpp_typecheck.error()
        << "template argument must be constant" << messaget::eom;
      throw 0;
    }

    const auto integer_bits = numeric_cast<mp_integer>(argument1);

    if(!integer_bits.has_value())
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be constant" << messaget::eom;
      throw 0;
    }

    if(*width < 1)
    {
      cpp_typecheck.error().source_location = argument0.find_source_location();
      cpp_typecheck.error()
        << "template argument must be greater than zero" << messaget::eom;
      throw 0;
    }

    if(*integer_bits < 0)
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be greater or equal zero" << messaget::eom;
      throw 0;
    }

    if(*integer_bits > *width)
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be smaller or equal width" << messaget::eom;
      throw 0;
    }

    dest = type_exprt(typet(base_name));
    dest.type().set(ID_width, integer2string(*width));
    dest.type().set(ID_integer_bits, integer2string(*integer_bits));
  }
  else if(base_name == ID_integer)
  {
    if(!arguments.empty())
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects no template arguments" << messaget::eom;
      throw 0;
    }

    dest = type_exprt(typet(base_name));
  }
  else if(base_name.starts_with("constant_infinity"))
  {
    // ok, but type missing
    dest = exprt(ID_infinity, size_type());
  }
  else if(base_name == "dump_scopes")
  {
    dest = exprt(ID_constant, typet(ID_empty));
    cpp_typecheck.warning()
      << "Scopes in location " << source_location << messaget::eom;
    cpp_typecheck.cpp_scopes.get_root_scope().print(cpp_typecheck.warning());
  }
  else if(base_name == "current_scope")
  {
    dest = exprt(ID_constant, typet(ID_empty));
    cpp_typecheck.warning() << "Scope in location " << source_location << ": "
                            << original_scope->prefix << messaget::eom;
  }
  else if(base_name == ID_size_t)
  {
    dest = type_exprt(size_type());
  }
  else if(base_name == ID_ssize_t)
  {
    dest = type_exprt(signed_size_type());
  }
  else
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "unknown built-in identifier: " << base_name
                          << messaget::eom;
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
  PRECONDITION(!cpp_name.get_sub().empty());

  original_scope = &cpp_typecheck.cpp_scopes.current_scope();
  source_location = cpp_name.source_location();

  irept::subt::const_iterator pos = cpp_name.get_sub().begin();

  bool recursive = true;

  // check if we need to go to the root scope
  if(pos->id() == "::")
  {
    pos++;
    cpp_typecheck.cpp_scopes.go_to_root_scope();
    recursive = false;
  }

  std::string final_base_name;
  template_args.make_nil();

  while(pos != cpp_name.get_sub().end())
  {
    if(pos->id() == ID_name)
      final_base_name += pos->get_string(ID_identifier);
    else if(pos->id() == ID_decltype)
    {
      exprt expr = static_cast<const exprt &>(pos->find(ID_type_arg));
      if(expr.is_nil())
        expr = static_cast<const exprt &>(pos->find(ID_expr_arg));
      if(expr.is_nil())
        expr = static_cast<const exprt &>(pos->find("expr"));
      if(expr.is_not_nil())
      {
        // Apply template_map to substitute template parameters
        // in the decltype expression (e.g., __test<_Tp>(nullptr))
        cpp_typecheck.template_map.apply(expr);
        cpp_typecheck.typecheck_expr(expr);
        typet t = expr.type();
        // Remove references
        if(
          t.id() == ID_pointer &&
          (t.get_bool(ID_C_reference) || t.get_bool(ID_C_rvalue_reference)))
          t = to_pointer_type(t).base_type();
        if(t.id() == ID_struct_tag)
        {
          cpp_typecheck.elaborate_class_template(t);
          const irep_idt &scope_id = to_struct_tag_type(t).get_identifier();
          cpp_typecheck.cpp_scopes.go_to(
            cpp_typecheck.cpp_scopes.get_scope(scope_id));
        }
        else
        {
          // decltype resolved to a non-class type; cannot scope into it.
          throw 0; // decltype resolved to non-class type
        }
      }
      final_base_name.clear();
    }
    else if(pos->id() == ID_template_args)
      template_args = to_cpp_template_args_non_tc(*pos);
    else if(pos->id() == "::")
    {
      // If final_base_name is empty, the scope was already navigated
      // (e.g., by a decltype handler). Just advance past ::.
      if(final_base_name.empty() && template_args.is_nil())
      {
        ++pos;
        continue;
      }
      if(cpp_typecheck.suppress_elaborate && template_args.is_nil())
      {
        // Fast path: use RECURSIVE lookup but only accept scopes.
        // Skip the expensive filter_for_named_scopes.
        auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED);
        bool found = false;
        for(const auto *id_ptr : id_set)
        {
          if(id_ptr->is_scope)
          {
            cpp_typecheck.cpp_scopes.go_to(
              static_cast<cpp_scopet &>(const_cast<cpp_idt &>(*id_ptr)));
            found = true;
            break;
          }
          if(id_ptr->is_typedef())
          {
            // Follow typedef to find the scope
            const auto *sym =
              cpp_typecheck.symbol_table.lookup(id_ptr->identifier);
            if(sym && sym->is_type && sym->type.id() == ID_struct_tag)
            {
              auto it = cpp_typecheck.cpp_scopes.id_map.find(
                to_struct_tag_type(sym->type).get_identifier());
              if(
                it != cpp_typecheck.cpp_scopes.id_map.end() &&
                it->second->is_scope)
              {
                cpp_typecheck.cpp_scopes.go_to(
                  static_cast<cpp_scopet &>(*it->second));
                found = true;
                break;
              }
            }
          }
        }
        if(found)
        {
          final_base_name.clear();
          ++pos;
          continue;
        }
        // Check if the name is a struct_tag identifier that has a
        // registered scope (e.g., an elaborated template class).
        // The name might be a full identifier (tag-X) or a base name
        // from template_map substitution. Try both.
        {
          auto it = cpp_typecheck.cpp_scopes.id_map.find(final_base_name);
          if(it == cpp_typecheck.cpp_scopes.id_map.end())
          {
            // Try with current scope prefix
            const std::string &scope_id =
              id2string(cpp_typecheck.cpp_scopes.current_scope().identifier);
            if(!scope_id.empty())
              it = cpp_typecheck.cpp_scopes.id_map.find(
                scope_id + "::" + id2string(final_base_name));
          }
          if(it == cpp_typecheck.cpp_scopes.id_map.end())
          {
            // Try as tag identifier
            it = cpp_typecheck.cpp_scopes.id_map.find(
              "tag-" + id2string(final_base_name));
          }
          if(
            it != cpp_typecheck.cpp_scopes.id_map.end() && it->second->is_scope)
          {
            cpp_typecheck.cpp_scopes.go_to(
              static_cast<cpp_scopet &>(*it->second));
            final_base_name.clear();
            ++pos;
            continue;
          }
        }
        // Check template_map for template parameters like _Up::X
        {
          typet mapped{};
          for(const auto &entry : cpp_typecheck.template_map.type_map)
          {
            const std::string &key = id2string(entry.first);
            auto p = key.rfind("::");
            std::string suffix =
              p != std::string::npos ? key.substr(p + 2) : key;
            if(
              suffix == id2string(final_base_name) &&
              entry.second.id() != ID_unassigned && entry.second.id() != ID_nil)
            {
              mapped = entry.second;
              break;
            }
          }
          if(mapped.is_not_nil() && mapped.id() == ID_struct_tag)
          {
            const irep_idt &scope_id =
              to_struct_tag_type(mapped).get_identifier();
            auto it = cpp_typecheck.cpp_scopes.id_map.find(scope_id);
            if(
              it != cpp_typecheck.cpp_scopes.id_map.end() &&
              it->second->is_scope)
            {
              cpp_typecheck.cpp_scopes.go_to(
                static_cast<cpp_scopet &>(*it->second));
              final_base_name.clear();
              ++pos;
              continue;
            }
          }
        }
        // Scope not found with suppress — bail out
        // Try to elaborate template class instances before giving up.
        // The name might be a struct_tag identifier (e.g.,
        // "std::__1::tag-__wrap_iter<ptr_signed_int>") that the scope
        // system doesn't know about. Look it up in the symbol table.
        {
          const auto *sym = cpp_typecheck.symbol_table.lookup(final_base_name);
          if(
            sym && sym->type.get_bool(ID_template_class_instance) &&
            (sym->type.id() == ID_struct || sym->type.id() == ID_union))
          {
            bool old_suppress = cpp_typecheck.suppress_elaborate;
            bool old_force = cpp_typecheck.force_elaborate;
            cpp_typecheck.suppress_elaborate = false;
            cpp_typecheck.force_elaborate = true;
            try
            {
              typet tag_type =
                sym->type.id() == ID_struct
                  ? static_cast<typet>(struct_tag_typet{sym->name})
                  : static_cast<typet>(union_tag_typet{sym->name});
              cpp_typecheck.elaborate_class_template(tag_type);
            }
            catch(...)
            {
            }
            cpp_typecheck.suppress_elaborate = old_suppress;
            cpp_typecheck.force_elaborate = old_force;
            // After elaboration, the scope should be registered
            auto it = cpp_typecheck.cpp_scopes.id_map.find(sym->name);
            if(
              it != cpp_typecheck.cpp_scopes.id_map.end() &&
              it->second->is_scope)
            {
              cpp_typecheck.cpp_scopes.go_to(
                static_cast<cpp_scopet &>(*it->second));
              final_base_name.clear();
              ++pos;
              continue;
            }
          }
        }
        throw 0;
      }

      if(template_args.is_not_nil())
      {
        auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED,
          cpp_idt::id_classt::TEMPLATE);

        // If no template was found, check if the name is a template
        // template parameter and resolve it via the template map.
        if(id_set.empty())
        {
          const auto param_set =
            cpp_typecheck.cpp_scopes.current_scope().lookup(
              final_base_name,
              recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED,
              cpp_idt::id_classt::TEMPLATE_PARAMETER);
          if(!param_set.empty())
          {
            const cpp_idt &param_id = **param_set.begin();
            exprt e = cpp_typecheck.template_map.lookup(param_id.identifier);
            if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
            {
              const std::string id_str = id2string(param_id.identifier);
              auto p = id_str.rfind("::");
              if(p != std::string::npos)
                e = cpp_typecheck.template_map.lookup_by_suffix(
                  id_str.substr(p + 2));
            }
            if(
              e.id() == ID_type &&
              e.type().id() == ID_template_parameter_symbol_type)
            {
              const irep_idt &tmpl_id =
                to_template_parameter_symbol_type(e.type()).get_identifier();
              if(cpp_typecheck.symbol_table.has_symbol(tmpl_id))
              {
                const symbolt &tmpl_sym = cpp_typecheck.lookup(tmpl_id);
                auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
                  tmpl_sym.base_name,
                  cpp_scopet::RECURSIVE,
                  cpp_idt::id_classt::TEMPLATE);
                for(const auto &f : found)
                  id_set.insert(f);
              }
            }
          }
        }

#ifdef DEBUG
        std::cout << "S: "
                  << cpp_typecheck.cpp_scopes.current_scope().identifier
                  << '\n';
        cpp_typecheck.cpp_scopes.current_scope().print(std::cout);
        std::cout << "X: " << id_set.size() << '\n';
#endif
        // Check if this is a template alias rather than a class template
        bool is_alias = false;
        for(const auto &id_ptr : id_set)
        {
          const symbolt &s = cpp_typecheck.lookup(id_ptr->identifier);
          if(
            s.type.get_bool(ID_is_template) &&
            to_cpp_declaration(s.type).is_template_alias())
          {
            is_alias = true;
            break;
          }
        }

        if(is_alias)
        {
          typet result =
            resolve_template_alias(final_base_name, id_set, template_args);
          if(result.id() == ID_struct_tag)
          {
            struct_tag_typet instance = to_struct_tag_type(result);
            instance.add_source_location() = source_location;
            cpp_typecheck.elaborate_class_template(instance);
            cpp_typecheck.cpp_scopes.go_to(
              cpp_typecheck.cpp_scopes.get_scope(instance.get_identifier()));
          }
          else
          {
            cpp_typecheck.error().source_location = source_location;
            cpp_typecheck.error()
              << "template alias '" << final_base_name
              << "' does not resolve to a class type" << messaget::eom;
            throw 0;
          }
        }
        else
        {
          typet instance = disambiguate_template_classes(
            final_base_name, id_set, template_args);

          instance.add_source_location() = source_location;

          // the "::" triggers template elaboration.
          // When suppress_elaborate is true (e.g., during class body
          // processing), force elaboration so that scope resolution
          // can access the template class's members.
          cpp_typecheck.elaborate_class_template(instance);

          cpp_typecheck.cpp_scopes.go_to(cpp_typecheck.cpp_scopes.get_scope(
            to_tag_type(instance).get_identifier()));
        }

        template_args.make_nil();
      }
      else
      {
        auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED);

        // If the name resolves to a template parameter, substitute it
        // with the actual type from the template map and use that type's
        // scope for the qualified lookup.
        if(!id_set.empty())
        {
          const cpp_idt &first = **id_set.begin();
          if(first.id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
          {
            exprt e = convert_template_parameter(first);
            if(e.id() == ID_type && e.type().id() == ID_struct_tag)
            {
              cpp_typecheck.elaborate_class_template(e.type());
              const irep_idt &scope_id =
                to_struct_tag_type(e.type()).get_identifier();
              cpp_typecheck.cpp_scopes.go_to(
                cpp_typecheck.cpp_scopes.get_scope(scope_id));
              template_args.make_nil();
              final_base_name.clear();
              pos++;
              continue;
            }
          }
        }

        filter_for_named_scopes(id_set);

        // If no named scope found, check for typedefs resolving to a
        // class type (e.g., typedef Base _Mybase; using _Mybase::_Mybase)
        if(id_set.empty())
        {
          auto typedef_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
            final_base_name, cpp_scopet::RECURSIVE);
          for(const auto &id_ptr : typedef_set)
          {
            if(id_ptr->id_class == cpp_idt::id_classt::TYPEDEF)
            {
              const symbolt *sym =
                cpp_typecheck.symbol_table.lookup(id_ptr->identifier);
              if(sym != nullptr && sym->is_type)
              {
                typet t = sym->type;
                if(t.id() == ID_struct_tag)
                {
                  cpp_typecheck.elaborate_class_template(t);
                  const irep_idt &scope_id =
                    to_struct_tag_type(t).get_identifier();
                  cpp_typecheck.cpp_scopes.go_to(
                    cpp_typecheck.cpp_scopes.get_scope(scope_id));
                  final_base_name.clear();
                  ++pos;
                  final_base_name.clear();
                  break;
                }
              }
            }
          }
          if(final_base_name.empty())
            continue; // typedef resolved, continue with next component
        }

        if(id_set.empty())
        {
          // Fallback: search the global id_map for the namespace.
          // This handles cases where the current scope (e.g., a
          // template instantiation scope) doesn't have the target
          // namespace in its parent chain.
          for(auto &entry : cpp_typecheck.cpp_scopes.id_map)
          {
            if(
              entry.second->base_name == final_base_name &&
              entry.second->is_namespace())
            {
              id_set.insert(entry.second);
            }
          }
        }

        if(id_set.empty())
        {
          if(final_base_name.empty())
          {
            ++pos;
            continue;
          }
          // Check id_map for struct_tag identifiers from
          // template_map substitution (e.g., tag-A::value_type).
          auto id_it = cpp_typecheck.cpp_scopes.id_map.find(final_base_name);
          if(
            id_it != cpp_typecheck.cpp_scopes.id_map.end() &&
            id_it->second->is_scope)
          {
            cpp_typecheck.cpp_scopes.go_to(
              static_cast<cpp_scopet &>(*id_it->second));

            // Trigger class elaboration so that base-class members
            // (e.g., inherited typedefs) are available for the
            // subsequent qualified lookup.
            if(!cpp_typecheck.cpp_scopes.current_scope()
                  .class_identifier.empty())
            {
              struct_tag_typet instance{
                cpp_typecheck.cpp_scopes.current_scope().class_identifier};
              cpp_typecheck.elaborate_class_template(instance);
            }

            final_base_name.clear();
            ++pos;
            continue;
          }
          if(cpp_typecheck.suppress_elaborate)
            throw 0;
          cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
          cpp_typecheck.error().source_location = source_location;
          cpp_typecheck.error()
            << "scope '" << final_base_name << "' not found" << messaget::eom;
          throw 0;
        }
        else if(id_set.size() >= 2)
        {
          cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
          cpp_typecheck.error().source_location = source_location;
          cpp_typecheck.error() << "scope '" << final_base_name
                                << "' is ambiguous" << messaget::eom;
          throw 0;
        }

        CHECK_RETURN(id_set.size() == 1);

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
    else if(pos->id() == ID_operator)
    {
      final_base_name += "operator";

      irept::subt::const_iterator next = pos + 1;
      CHECK_RETURN(next != cpp_name.get_sub().end());

      if(
        next->id() == ID_cpp_name || next->id() == ID_pointer ||
        next->id() == ID_frontend_pointer || next->id() == ID_int ||
        next->id() == ID_char || next->id() == ID_c_bool ||
        next->id() == ID_merged_type)
      {
        // it's a cast operator
        irept next_ir = *next;
        typet op_name;
        op_name.swap(next_ir);
        cpp_typecheck.typecheck_type(op_name);
        final_base_name += "(" + cpp_type2name(op_name) + ")";
        pos++;
      }
    }
    else
    {
      final_base_name += pos->id_string();
      // Substitute destructor names: when "~" is followed by a name
      // that's a template parameter, replace it with the actual type.
      if(
        pos->id_string() == "~" && (pos + 1) != cpp_name.get_sub().end() &&
        (pos + 1)->id() == ID_name)
      {
        irep_idt param_name = (pos + 1)->get(ID_identifier);
        for(const auto &entry : cpp_typecheck.template_map.type_map)
        {
          const std::string &key = id2string(entry.first);
          auto p = key.rfind("::");
          std::string suffix = p != std::string::npos ? key.substr(p + 2) : key;
          if(
            suffix == id2string(param_name) &&
            entry.second.id() != ID_unassigned && entry.second.id() != ID_nil &&
            entry.second.id() == ID_struct_tag)
          {
            // Skip the name sub-node (it will be replaced)
            ++pos;
            // Use the struct's base name for the destructor
            irep_idt tag = to_struct_tag_type(entry.second).get_identifier();
            std::string tag_str = id2string(tag);
            auto last_sep = tag_str.rfind("::");
            if(last_sep != std::string::npos)
              tag_str = tag_str.substr(last_sep + 2);
            if(tag_str.substr(0, 4) == "tag-")
              tag_str = tag_str.substr(4);
            auto angle = tag_str.find('<');
            if(angle != std::string::npos)
              tag_str = tag_str.substr(0, angle);
            final_base_name += tag_str;
            break;
          }
        }
      }
    }

    pos++;
  }

  base_name = final_base_name;

  return cpp_typecheck.cpp_scopes.current_scope();
}

/// disambiguate partial specialization
typet cpp_typecheck_resolvet::disambiguate_template_classes(
  const irep_idt &base_name,
  const cpp_scopest::id_sett &id_set,
  const cpp_template_args_non_tct &full_template_args)
{
  cpp_scopest::id_sett effective_id_set = id_set;

  if(effective_id_set.empty())
  {
    // The template may not be visible in the current scope (e.g.,
    // during template instantiation). Search from the root scope.
    effective_id_set = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
      base_name, cpp_scopet::RECURSIVE, cpp_idt::id_classt::TEMPLATE);
  }

  // If still not found, search the symbol table for class templates
  // with the matching base name. This handles cases where the class
  // template was not added to the scope tree (e.g., templates from
  // system headers that were parsed but not fully registered).
  if(effective_id_set.empty())
  {
    for(const auto &sym_pair : cpp_typecheck.symbol_table)
    {
      const symbolt &sym = sym_pair.second;
      if(
        sym.base_name == base_name && sym.type.get_bool(ID_is_template) &&
        to_cpp_declaration(sym.type).is_class_template())
      {
        auto it = cpp_typecheck.cpp_scopes.id_map.find(sym.name);
        if(
          it != cpp_typecheck.cpp_scopes.id_map.end() &&
          (it->second->id_class == cpp_idt::id_classt::TEMPLATE ||
           it->second->is_template_scope()))
        {
          effective_id_set.insert(it->second);
        }
      }
    }
  }

  if(effective_id_set.empty())
  {
    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template scope '" << base_name << "' not found"
                          << messaget::eom;
    throw 0;
  }

  std::set<irep_idt> primary_templates;

  for(const auto &id_ptr : effective_id_set)
  {
    irep_idt id = id_ptr->identifier;
    // For template scopes found via id_map, the identifier might be
    // empty. Look up the id_map key instead.
    if(id.empty() || !cpp_typecheck.symbol_table.has_symbol(id))
    {
      for(const auto &entry : cpp_typecheck.cpp_scopes.id_map)
      {
        if(entry.second == id_ptr)
        {
          id = entry.first;
          break;
        }
      }
    }
    if(!cpp_typecheck.symbol_table.has_symbol(id))
      continue;
    const symbolt &s = cpp_typecheck.lookup(id);
    if(!s.type.get_bool(ID_is_template))
      continue;
    const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);
    if(!cpp_declaration.is_class_template())
      continue;
    irep_idt specialization_of = cpp_declaration.get_specialization_of();
    if(!specialization_of.empty())
      primary_templates.insert(specialization_of);
    else
      primary_templates.insert(id);
  }

  if(primary_templates.empty())
  {
    // The id_set may contain non-class templates (e.g., constructor
    // templates of an instantiated class) that shadow the class
    // template with the same base name. Walk up from each candidate's
    // parent scope to find the actual class template.
    for(const auto &id_ptr : effective_id_set)
    {
      auto it = cpp_typecheck.cpp_scopes.id_map.find(id_ptr->identifier);
      if(it == cpp_typecheck.cpp_scopes.id_map.end())
        continue;
      cpp_scopet &scope_ref = static_cast<cpp_scopet &>(*it->second);
      cpp_scopet *scope = &scope_ref;
      while(!scope->is_root_scope())
      {
        scope = &scope->get_parent();
        auto found = scope->lookup(
          base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);
        for(const auto &fid : found)
        {
          if(!cpp_typecheck.symbol_table.has_symbol(fid->identifier))
            continue;
          const symbolt &fs = cpp_typecheck.lookup(fid->identifier);
          if(!fs.type.get_bool(ID_is_template))
            continue;
          const cpp_declarationt &fd = to_cpp_declaration(fs.type);
          if(!fd.is_class_template())
            continue;
          irep_idt spec = fd.get_specialization_of();
          primary_templates.insert(spec.empty() ? fid->identifier : spec);
        }
        if(!primary_templates.empty())
          break;
      }
      if(!primary_templates.empty())
        break;
    }
  }

  if(primary_templates.empty())
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template '" << base_name << "' not found"
                          << messaget::eom;
    throw 0;
  }

  if(primary_templates.size() >= 2)
  {
    // Multiple primary templates found. Filter by the current scope:
    // only keep templates whose identifier is within the scope that
    // resolve_scope navigated to via :: qualifiers.
    cpp_scopet &current = cpp_typecheck.cpp_scopes.current_scope();
    const std::string prefix = id2string(current.identifier) + "::";
    std::set<irep_idt> filtered;
    for(const auto &pt : primary_templates)
    {
      if(id2string(pt).find(prefix) == 0 || pt == current.identifier)
        filtered.insert(pt);
    }
    if(filtered.size() == 1)
      primary_templates = filtered;
  }

  if(primary_templates.size() >= 2)
  {
    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template scope '" << base_name << "' is ambiguous"
                          << messaget::eom;
    throw 0;
  }

  const symbolt &primary_template_symbol =
    cpp_typecheck.lookup(*primary_templates.begin());

  // We typecheck the template arguments in the context
  // of the original scope!
  cpp_template_args_tct full_template_args_tc;

  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.cpp_scopes.go_to(*original_scope);

    // use template type of 'primary template'
    full_template_args_tc = cpp_typecheck.typecheck_template_args(
      source_location, primary_template_symbol, full_template_args);

    for(auto &arg : full_template_args_tc.arguments())
    {
      if(arg.id() == ID_type)
        continue;
      if(arg.id() == ID_symbol)
      {
        const symbol_exprt &s = to_symbol_expr(arg);
        const symbolt &symbol = cpp_typecheck.lookup(s.get_identifier());

        if(
          cpp_typecheck.cpp_is_pod(symbol.type) &&
          symbol.type.get_bool(ID_C_constant))
        {
          arg = symbol.value;
        }
      }
      simplify(arg, cpp_typecheck);
    }

    // go back to where we used to be
  }

  // find any matches

  std::vector<matcht> matches;

  // the baseline
  matches.push_back(matcht(
    full_template_args_tc,
    full_template_args_tc,
    primary_template_symbol.name));

  for(const auto &id_ptr : id_set)
  {
    const irep_idt id = id_ptr->identifier;
    const symbolt &s = cpp_typecheck.lookup(id);

    if(s.type.get(ID_specialization_of).empty())
      continue;

    const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);

    const cpp_template_args_non_tct &partial_specialization_args =
      cpp_declaration.partial_specialization_args();

    // alright, set up template arguments as 'unassigned'

    cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.template_map.build_unassigned(
      cpp_declaration.template_type());

    // iterate over template instance
    if(
      full_template_args_tc.arguments().size() !=
      partial_specialization_args.arguments().size())
    {
      continue;
    }

    // we need to do this in the right scope

    cpp_scopet *template_scope =
      static_cast<cpp_scopet *>(cpp_typecheck.cpp_scopes.id_map[id]);

    if(template_scope == nullptr)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << "template identifier: " << id << '\n'
        << "class template instantiation error" << messaget::eom;
      throw 0;
    }

    // enter the scope of the template
    cpp_typecheck.cpp_scopes.go_to(*template_scope);

    for(std::size_t i = 0; i < full_template_args_tc.arguments().size(); i++)
    {
      if(full_template_args_tc.arguments()[i].id() == ID_type)
        guess_template_args(
          partial_specialization_args.arguments()[i].type(),
          full_template_args_tc.arguments()[i].type());
      else
        guess_template_args(
          partial_specialization_args.arguments()[i],
          full_template_args_tc.arguments()[i]);
    }

    // see if that has worked out

    cpp_template_args_tct guessed_template_args =
      cpp_typecheck.template_map.build_template_args(
        cpp_declaration.template_type());

    if(!guessed_template_args.has_unassigned())
    {
      // check: we can now typecheck the partial_specialization_args
      // If typechecking fails (e.g., accessing a member of a non-class
      // type), treat it as a substitution failure (SFINAE) and skip
      // this specialization.
      cpp_template_args_tct partial_specialization_args_tc;
      bool sfinae_failed = false;
      {
        null_message_handlert null_handler;
        message_handlert &old_handler = cpp_typecheck.get_message_handler();
        cpp_typecheck.set_message_handler(null_handler);
        try
        {
          partial_specialization_args_tc =
            cpp_typecheck.typecheck_template_args(
              source_location,
              primary_template_symbol,
              partial_specialization_args);
        }
        catch(...)
        {
          sfinae_failed = true;
        }
        cpp_typecheck.set_message_handler(old_handler);
      }
      if(sfinae_failed)
        continue;

      // if these match the arguments, we have a match

      // Strip ellipsis flags from cpp_declaration declarators in code
      // type arguments. When a variadic pack parameter (Args...) is
      // substituted with concrete types, the ellipsis flag remains on
      // the declarator but is absent from the full template args.
      for(auto &arg : partial_specialization_args_tc.arguments())
      {
        if(arg.id() != ID_type || arg.type().id() != ID_code)
          continue;
        for(auto &param : arg.type().add(ID_parameters).get_sub())
        {
          if(param.id() != ID_cpp_declaration)
            continue;
          for(auto &decl : static_cast<cpp_declarationt &>(param).declarators())
            decl.remove(ID_ellipsis);
        }
      }

      DATA_INVARIANT(
        partial_specialization_args_tc.arguments().size() ==
          full_template_args_tc.arguments().size(),
        "argument numbers must match");

      if(partial_specialization_args_tc == full_template_args_tc)
      {
        // Also check that cv-qualifiers and #c_type match, since
        // operator== ignores #-prefixed attributes like C_constant,
        // C_volatile, and C_c_type (needed to distinguish char from
        // signed char, and const T* from T*).
        bool qualifiers_match = true;
        for(std::size_t j = 0;
            j < partial_specialization_args_tc.arguments().size();
            j++)
        {
          const exprt &p = partial_specialization_args_tc.arguments()[j];
          const exprt &f = full_template_args_tc.arguments()[j];
          if(p.id() == ID_type)
          {
            if(
              !qualifiers_match_recursively(p.type(), f.type()) ||
              p.type().get(ID_C_c_type) != f.type().get(ID_C_c_type))
            {
              qualifiers_match = false;
              break;
            }
          }
        }

        if(qualifiers_match)
        {
          // Count constrained arguments: arguments in the partial
          // specialization pattern that are not just a plain template
          // parameter name. More constrained = more specialized.
          // Also count repeated parameter names as constraints
          // (e.g., <T, T> constrains both args to be equal).
          std::size_t constrained = 0;
          std::size_t repeated_params = 0;
          std::set<irep_idt> seen_params;
          for(const auto &arg : partial_specialization_args.arguments())
          {
            // Get the actual node, unwrapping ambiguous and type
            const irept *a = &arg;
            if(a->id() == ID_type)
              a = &arg.type();
            if(a->id() == ID_ambiguous)
              a = &a->find(ID_type);

            if(a->id() != ID_cpp_name)
            {
              constrained++;
            }
            else
            {
              // A cpp_name with template arguments (e.g., pack<Rp...>)
              // is more constrained than a plain name.
              bool has_tmpl_args = false;
              irep_idt param_name;
              for(const auto &sub : a->get_sub())
              {
                if(sub.id() == ID_template_args)
                {
                  has_tmpl_args = true;
                  break;
                }
                if(sub.id() == ID_name)
                  param_name = sub.get(ID_identifier);
              }
              if(has_tmpl_args)
                constrained++;
              else if(
                !param_name.empty() && !seen_params.insert(param_name).second)
              {
                // Same parameter used again — equality constraint
                constrained++;
                repeated_params++;
              }
            }
          }
          // Add weight from requires clause constraints.
          // Count the number of atomic constraints (type predicates,
          // function calls) in the expression for proper ordering
          // per [temp.constr.order].
          const auto &req_str =
            cpp_declaration.template_type().get(ID_C_requires_clause);
          if(!req_str.empty() && isdigit(id2string(req_str)[0]))
            constrained += std::stoull(id2string(req_str));
          else if(cpp_declaration.template_type()
                    .find(ID_C_requires_clause)
                    .is_not_nil())
          {
            const auto &req_expr =
              cpp_declaration.template_type().find(ID_C_requires_clause);
            // Count atomic constraints by visiting the expression tree
            std::function<std::size_t(const irept &)> count_atoms =
              [&](const irept &node) -> std::size_t
            {
              if(node.id() == ID_and || node.id() == ID_or)
              {
                std::size_t n = 0;
                for(const auto &sub : node.get_sub())
                  n += count_atoms(sub);
                return n;
              }
              if(node.id() == ID_not)
                return count_atoms(node.get_sub().front());
              return 1;
            };
            constrained += count_atoms(req_expr);
          }

          // [temp.constr.decl]: evaluate the requires clause to check
          // if the constraint is satisfied for the deduced arguments.
          // If not satisfied, skip this specialization.
          //
          // Only evaluate type-predicate constraints (e.g.,
          // __is_pointer(T)) that can be resolved without full
          // type-checking. Complex constraints are deferred to
          // elaborate_class_template.
          {
            const exprt &req_clause = static_cast<const exprt &>(
              cpp_declaration.template_type().find(ID_C_requires_clause));
            if(req_clause.is_not_nil() && req_clause.id() != ID_nil)
            {
              exprt req_copy = req_clause;
              cpp_typecheck.template_map.apply(req_copy);
              // Try to evaluate the constraint. Use typecheck_expr
              // in a safe context: suppress elaboration and catch
              // all errors. If evaluation fails, treat as satisfied
              // and let elaborate_class_template re-check later.
              null_message_handlert null_handler;
              message_handlert &old_handler =
                cpp_typecheck.get_message_handler();
              cpp_typecheck.set_message_handler(null_handler);
              bool satisfied = true;
              bool evaluated = false;
              // Only attempt evaluation for simple type predicates
              // and boolean combinations. Skip complex expressions
              // that might trigger invariant violations.
              if(
                req_copy.id() == ID_and || req_copy.id() == ID_or ||
                id2string(req_copy.id()).find("__is_") == 0 ||
                id2string(req_copy.id()).find("__has_") == 0)
              {
                try
                {
                  cpp_typecheck.typecheck_expr(req_copy);
                  simplify(req_copy, cpp_typecheck);
                  if(req_copy.is_false())
                    satisfied = false;
                  evaluated = true;
                }
                catch(...)
                {
                }
              }
              cpp_typecheck.set_message_handler(old_handler);
              if(evaluated && !satisfied)
                continue;
            }
          }

          matches.push_back(matcht(
            guessed_template_args,
            full_template_args_tc,
            id,
            constrained,
            repeated_params));
        }
      }
    }
  }

  CHECK_RETURN(!matches.empty());

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

  const matcht &match = *matches.begin();

  const symbolt &choice = cpp_typecheck.lookup(match.id);

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
    cpp_typecheck.error() << "template '"
                      << base_name << "' is not a class" << messaget::eom;
    throw 0;
  }

  struct_tag_typet result(instance.name);
  result.add_source_location()=source_location;

  return result;
#else

  // build instance
  const symbolt &instance = cpp_typecheck.class_template_symbol(
    source_location, choice, match.specialization_args, match.full_args);

  typet result;
  if(instance.type.id() == ID_union)
    result = union_tag_typet(instance.name);
  else
    result = struct_tag_typet(instance.name);
  result.add_source_location() = source_location;

  return result;
#endif
}

typet cpp_typecheck_resolvet::resolve_template_alias(
  const irep_idt &base_name,
  const cpp_scopest::id_sett &id_set,
  const cpp_template_args_non_tct &full_template_args)
{
  // find the template alias symbol
  const symbolt *template_sym = nullptr;
  for(const auto &id_ptr : id_set)
  {
    const symbolt &s = cpp_typecheck.lookup(id_ptr->identifier);
    if(!s.type.get_bool(ID_is_template))
      continue;
    if(to_cpp_declaration(s.type).is_template_alias())
    {
      template_sym = &s;
      break;
    }
  }

  INVARIANT(template_sym != nullptr, "template alias symbol must exist");

  // typecheck template arguments
  cpp_template_args_tct template_args_tc;
  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
    cpp_typecheck.cpp_scopes.go_to(*original_scope);
    template_args_tc = cpp_typecheck.typecheck_template_args(
      source_location, *template_sym, full_template_args);
  }

  const symbolt &instance = cpp_typecheck.instantiate_template(
    source_location, *template_sym, template_args_tc, template_args_tc);

  return instance.type;
}

cpp_scopet &cpp_typecheck_resolvet::resolve_namespace(const cpp_namet &cpp_name)
{
  irep_idt base_name;
  cpp_template_args_non_tct template_args;
  template_args.make_nil();

  cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
  resolve_scope(cpp_name, base_name, template_args);

  // Substitute destructor names: ~_Tp where _Tp is a template parameter.
  if(
    !base_name.empty() && id2string(base_name)[0] == '~' &&
    id2string(base_name).size() > 1)
  {
    std::string after_tilde = id2string(base_name).substr(1);
    for(const auto &entry : cpp_typecheck.template_map.type_map)
    {
      const std::string &key = id2string(entry.first);
      auto p = key.rfind("::");
      std::string suffix = p != std::string::npos ? key.substr(p + 2) : key;
      if(
        suffix == after_tilde && entry.second.id() != ID_unassigned &&
        entry.second.id() != ID_nil && entry.second.id() == ID_struct_tag)
      {
        // Get the struct's base name for the destructor
        const irep_idt &tag = to_struct_tag_type(entry.second).get_identifier();
        std::string tag_str = id2string(tag);
        // Extract unqualified name
        auto last_sep = tag_str.rfind("::");
        if(last_sep != std::string::npos)
          tag_str = tag_str.substr(last_sep + 2);
        if(tag_str.substr(0, 4) == "tag-")
          tag_str = tag_str.substr(4);
        // Remove template args for destructor name
        auto angle = tag_str.find('<');
        if(angle != std::string::npos)
          tag_str = tag_str.substr(0, angle);
        base_name = "~" + tag_str;
        break;
      }
    }
  }

  bool qualified = cpp_name.is_qualified();
  (void)qualified;

  auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
    base_name, cpp_scopet::RECURSIVE);

  filter_for_namespaces(id_set);

  if(id_set.empty())
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "namespace '" << base_name << "' not found"
                          << messaget::eom;
    throw 0;
  }
  else if(id_set.size() == 1)
  {
    cpp_idt &id = **id_set.begin();
    return (cpp_scopet &)id;
  }
  else
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "namespace '" << base_name << "' is ambiguous"
                          << messaget::eom;
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

    if(id_expr.id() == ID_type)
    {
      out << "type " << cpp_typecheck.to_string(id_expr.type());
    }
    else
    {
      irep_idt id;

      if(id_expr.type().get_bool(ID_is_template))
        out << "template ";

      if(id_expr.id() == ID_member)
      {
        out << "member ";
        id = "." + id2string(base_name);
      }
      else if(id_expr.id() == ID_pod_constructor)
      {
        out << "constructor ";
        id.clear();
      }
      else if(id_expr.id() == ID_template_function_instance)
      {
        out << "symbol ";
      }
      else
      {
        out << "symbol ";
        id = cpp_typecheck.to_string(id_expr);
      }

      if(id_expr.type().get_bool(ID_is_template))
      {
      }
      else if(id_expr.type().id() == ID_code)
      {
        const code_typet &code_type = to_code_type(id_expr.type());
        const typet &return_type = code_type.return_type();
        const code_typet::parameterst &parameters = code_type.parameters();
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

      if(id_expr.id() == ID_symbol)
      {
        const symbolt &symbol = cpp_typecheck.lookup(to_symbol_expr(id_expr));
        out << " (" << symbol.location << ")";
      }
      else if(id_expr.id() == ID_template_function_instance)
      {
        const symbolt &symbol =
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

  original_scope = &cpp_typecheck.cpp_scopes.current_scope();
  cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

  // this changes the scope
  resolve_scope(cpp_name, base_name, template_args);

#ifdef DEBUG
  std::cout << "base name: " << base_name << '\n';
  std::cout << "template args: " << template_args.pretty() << '\n';
  std::cout << "original-scope: " << original_scope->prefix << '\n';
  std::cout << "scope: " << cpp_typecheck.cpp_scopes.current_scope().prefix
            << '\n';
#endif

  bool qualified = cpp_name.is_qualified();

  // do __CPROVER scope
  if(qualified)
  {
    if(cpp_typecheck.cpp_scopes.current_scope().identifier == "__CPROVER")
      return do_builtin(base_name, fargs, template_args);
  }
  else
  {
    if(
      base_name == "__func__" || base_name == "__FUNCTION__" ||
      base_name == "__PRETTY_FUNCTION__")
    {
      // __func__ is an ANSI-C standard compliant hack to get the function name
      // __FUNCTION__ and __PRETTY_FUNCTION__ are GCC-specific
      string_constantt s(source_location.get_function());
      s.add_source_location() = source_location;
      return std::move(s);
    }
  }

  cpp_scopest::id_sett id_set;

  cpp_scopet::lookup_kindt lookup_kind = cpp_scopet::RECURSIVE;

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

  // If no template was found, check if the name is a template template
  // parameter and resolve it via the template map.
  if(id_set.empty() && template_args.is_not_nil())
  {
    const auto param_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
      base_name, lookup_kind, cpp_idt::id_classt::TEMPLATE_PARAMETER);
    if(!param_set.empty())
    {
      const cpp_idt &param_id = **param_set.begin();
      exprt e = cpp_typecheck.template_map.lookup(param_id.identifier);
      if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
      {
        const std::string id_str = id2string(param_id.identifier);
        auto p = id_str.rfind("::");
        if(p != std::string::npos)
          e = cpp_typecheck.template_map.lookup_by_suffix(id_str.substr(p + 2));
      }
      if(
        e.id() == ID_type && e.type().id() == ID_template_parameter_symbol_type)
      {
        const irep_idt &tmpl_id =
          to_template_parameter_symbol_type(e.type()).get_identifier();
        // The template identifier is like "template.MyVec<Type0>" or
        // "std::template.MyVec<Type0>". Look up the template symbol
        // in the symbol table and find its scope entry.
        if(cpp_typecheck.symbol_table.has_symbol(tmpl_id))
        {
          const symbolt &tmpl_sym = cpp_typecheck.lookup(tmpl_id);
          irep_idt tmpl_base = tmpl_sym.base_name;
          // Search from root scope to find the template
          auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
            tmpl_base, cpp_scopet::RECURSIVE, cpp_idt::id_classt::TEMPLATE);
          for(const auto &f : found)
            id_set.insert(f);
        }
      }
    }
  }

  // Argument-dependent name lookup (ADL / Koenig lookup):
  // For unqualified calls, also search in the namespaces of the
  // argument types. This is required for e.g. operator+(string, string)
  // to be found when called from outside namespace std.
  if(!qualified && !fargs.has_object)
    resolve_with_arguments(id_set, base_name, fargs);

  if(id_set.empty() && qualified)
  {
    // The scope might be an un-elaborated template class instance.
    // Try to elaborate it and retry the lookup.
    const cpp_scopet &cur = cpp_typecheck.cpp_scopes.current_scope();
    const auto *scope_sym = cpp_typecheck.symbol_table.lookup(cur.identifier);
    if(
      scope_sym &&
      (scope_sym->type.id() == ID_struct || scope_sym->type.id() == ID_union) &&
      (scope_sym->type.get_bool(ID_template_class_instance) ||
       scope_sym->type.find(ID_C_template).is_not_nil()))
    {
      bool old_suppress = cpp_typecheck.suppress_elaborate;
      cpp_typecheck.suppress_elaborate = false;
      try
      {
        typet tag = scope_sym->type.id() == ID_struct
                      ? static_cast<typet>(struct_tag_typet{scope_sym->name})
                      : static_cast<typet>(union_tag_typet{scope_sym->name});
        cpp_typecheck.elaborate_class_template(tag);
      }
      catch(...)
      {
      }
      cpp_typecheck.suppress_elaborate = old_suppress;
      // Retry lookup after elaboration
      id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
        base_name, cpp_scopet::SCOPE_ONLY);
    }
  }

  if(id_set.empty())
  {
    if(!fail_with_exception)
      return nil_exprt();

    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location = source_location;

    if(qualified)
    {
      cpp_typecheck.error() << "symbol '" << base_name << "' not found";

      if(cpp_typecheck.cpp_scopes.current_scope().is_root_scope())
        cpp_typecheck.error() << " in root scope";
      else
        cpp_typecheck.error()
          << " in scope '" << cpp_typecheck.cpp_scopes.current_scope().prefix
          << "'";
    }
    else
    {
      // Destructor names (~X): destructors are implicitly noexcept
      // in C++11+. When a destructor can't be resolved (e.g., because
      // the class isn't fully elaborated during noexcept evaluation),
      // return a dummy noexcept destructor symbol instead of throwing.
      if(!base_name.empty() && id2string(base_name)[0] == '~')
      {
        // Destructor not found — return nil to signal failure
        // without throwing. The noexcept handler will catch this.
        if(!fail_with_exception)
          return nil_exprt();
        // For fail_with_exception=true, throw so the noexcept
        // handler's catch block returns true.
        throw 0;
      }
      // Template template parameters may have "template." prefix.
      // Strip it and retry.
      if(id2string(base_name).substr(0, 9) == "template.")
      {
        irep_idt stripped = id2string(base_name).substr(9);
        id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          stripped, qualified ? cpp_scopet::QUALIFIED : cpp_scopet::RECURSIVE);
        if(!id_set.empty())
          goto resolved_after_strip;
      }
      // C++ [dcl.link]: extern "C" only affects linkage, not name
      // lookup. Try tag-name fallback for struct/class/union tags.
      {
        irep_idt tag_name = "tag-" + id2string(base_name);
        const symbolt *tag_sym = cpp_typecheck.symbol_table.lookup(tag_name);
        if(tag_sym)
        {
          // Found as a tag — create a type expression
          struct_tag_typet tag_type(tag_name);
          exprt type_expr(ID_type);
          type_expr.type() = tag_type;
          type_expr.add_source_location() = source_location;
          return type_expr;
        }
      }
      cpp_typecheck.error() << "symbol '" << base_name << "' is unknown";
    }

    cpp_typecheck.error() << messaget::eom;
    throw 0;
  }
resolved_after_strip:

  resolve_identifierst identifiers;

  if(template_args.is_not_nil())
  {
    // first figure out if we are doing functions/methods or
    // classes
    bool have_classes = false, have_methods = false;
    bool have_aliases = false;

    for(auto it = id_set.begin(); it != id_set.end();)
    {
      const irep_idt id = (*it)->identifier;
      const symbolt &s = cpp_typecheck.lookup(id);
      if(!s.type.get_bool(ID_is_template))
      {
        it = id_set.erase(it);
        continue;
      }
      const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);
      if(cpp_declaration.is_template_alias())
        have_aliases = true;
      else if(cpp_declaration.is_class_template())
        have_classes = true;
      else
        have_methods = true;
      ++it;
    }

    if(want == wantt::BOTH && have_classes && have_methods)
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error() << "template symbol '" << base_name
                            << "' is ambiguous" << messaget::eom;
      throw 0;
    }

    if(have_aliases)
    {
      // template alias — instantiate and return the aliased type.
      // Substitution may fail (e.g., enable_if with false condition);
      // treat as SFINAE when fail_with_exception is false.
      try
      {
        typet result = resolve_template_alias(base_name, id_set, template_args);
        identifiers.push_back(exprt(ID_type, result));
      }
      catch(int)
      {
        if(fail_with_exception)
          throw;
        return nil_exprt();
      }
    }
    else if(want == wantt::TYPE || have_classes)
    {
      typet instance =
        disambiguate_template_classes(base_name, id_set, template_args);

      if(!cpp_typecheck.skip_typechecking_elaborate)
        cpp_typecheck.elaborate_class_template(instance);

      identifiers.push_back(exprt(ID_type, instance));
    }
    else
    {
      // Check for variable templates (concepts) with explicit args.
      // These need to be instantiated as variable templates, not
      // as function templates.
      bool handled_variable_template = false;
      if(template_args.is_not_nil())
      {
        for(const auto *id_ptr : id_set)
        {
          const symbolt &s = cpp_typecheck.lookup(id_ptr->identifier);
          if(!s.type.get_bool(ID_is_template))
            continue;
          const cpp_declarationt &decl = to_cpp_declaration(s.type);
          // Variable templates have declarators but are not class
          // templates and not function templates (no function type).
          // Skip partial specializations — they are matched later
          // by instantiate_template, not used for direct instantiation.
          if(decl.is_class_template() || decl.is_template_alias())
            continue;
          if(!s.type.get(ID_specialization_of).empty())
            continue;
          if(
            !decl.declarators().empty() &&
            decl.declarators()[0].type().id() != ID_function_type)
          {
            // This is a variable template (e.g., concept).
            // Instantiate with explicit template args.
            cpp_template_args_tct tc_args;
            try
            {
              tc_args = cpp_typecheck.typecheck_template_args(
                source_location, s, template_args);
            }
            catch(...)
            {
              continue;
            }
            const symbolt &inst_sym = cpp_typecheck.instantiate_template(
              source_location, s, tc_args, tc_args);
            // The instantiated symbol is a constexpr variable.
            // Return its value, evaluating any remaining constexpr
            // function calls.
            if(inst_sym.value.is_not_nil())
            {
              exprt val = inst_sym.value;
              if(!val.is_constant())
              {
                // Try constexpr evaluation of function calls
                std::function<void(exprt &)> eval_calls;
                eval_calls = [&](exprt &e)
                {
                  for(auto &op : e.operands())
                    eval_calls(op);
                  if(
                    e.id() == ID_side_effect &&
                    e.get(ID_statement) == ID_function_call)
                  {
                    exprt r = try_evaluate_constexpr(
                      e, cpp_typecheck.symbol_table, cpp_typecheck);
                    if(r.is_not_nil())
                      e = r;
                  }
                  simplify(e, cpp_typecheck);
                };
                eval_calls(val);
              }
              val.add_source_location() = source_location;
              identifiers.push_back(val);
              handled_variable_template = true;
            }
            else
            {
              // No value — return the symbol
              symbol_exprt sym_expr{inst_sym.name, inst_sym.type};
              sym_expr.add_source_location() = source_location;
              identifiers.push_back(sym_expr);
              handled_variable_template = true;
            }
            break;
          }
        }
      }
      if(!handled_variable_template)
      {
        // methods and functions
        convert_identifiers(id_set, fargs, identifiers);

        apply_template_args(identifiers, template_args, fargs);
      }
    }
  }
  else
  {
    convert_identifiers(id_set, fargs, identifiers);
  }

  // change types into constructors if we want a constructor
  if(want == wantt::VAR)
  {
    make_constructors(identifiers);
    remove_duplicates(identifiers);
  }

  filter(identifiers, want);

#ifdef DEBUG
  std::cout << "P0 " << base_name << " " << identifiers.size() << '\n';
  show_identifiers(base_name, identifiers, std::cout);
  std::cout << '\n';
#endif

  exprt result;

  // We disambiguate functions
  resolve_identifierst new_identifiers = identifiers;

  remove_templates(new_identifiers);

#ifdef DEBUG
  std::cout << "P1 " << base_name << " " << new_identifiers.size() << '\n';
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << '\n';
#endif

  // we only want _exact_ matches, without templates!
  exact_match_functions(new_identifiers, fargs);

#ifdef DEBUG
  std::cout << "P2 " << base_name << " " << new_identifiers.size() << '\n';
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << '\n';
#endif

  // no exact matches? Try again with function template guessing.
  if(new_identifiers.empty())
  {
    new_identifiers = identifiers;

    // C++20 concept subsumption: before instantiation, filter out
    // templates subsumed by more constrained ones.
    if(new_identifiers.size() > 1)
    {
      auto get_tmpl_concepts = [&](const exprt &id) -> std::string
      {
        irep_idt sym_id = id.get(ID_identifier);
        if(sym_id.empty())
          return {};
        const auto *sym = cpp_typecheck.symbol_table.lookup(sym_id);
        if(!sym || !sym->type.get_bool(ID_is_template))
          return {};
        const cpp_declarationt &decl = to_cpp_declaration(sym->type);
        for(const auto &p : decl.template_type().template_parameters())
        {
          const irep_idt &cc = p.get("#C_concept_constraint");
          if(!cc.empty())
            return id2string(cc);
        }
        const auto &req_expr = decl.template_type().find(ID_C_requires_clause);
        if(req_expr.is_not_nil() && req_expr.id() != ID_nil)
        {
          std::string concepts;
          std::function<void(const irept &)> visit = [&](const irept &node)
          {
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
          return concepts;
        }
        return {};
      };

      auto concept_subsumes =
        [&](const std::string &cj, const std::string &ci) -> bool
      {
        if(cj == ci)
          return false;
        if(cj.find(ci) != std::string::npos)
          return true;
        // Look up concept template definition
        for(const auto &entry : cpp_typecheck.symbol_table)
        {
          if(
            id2string(entry.second.base_name) != cj ||
            !entry.second.type.get_bool(ID_is_template))
            continue;
          bool found = false;
          std::function<void(const irept &)> search = [&](const irept &node)
          {
            if(found)
              return;
            if(node.id() == ID_name && id2string(node.get(ID_identifier)) == ci)
              found = true;
            for(const auto &sub : node.get_sub())
              search(sub);
            for(const auto &named : node.get_named_sub())
              search(named.second);
          };
          search(entry.second.type);
          if(found)
            return true;
        }
        return false;
      };

      std::vector<std::string> constraints;
      for(const auto &id : new_identifiers)
        constraints.push_back(get_tmpl_concepts(id));

      std::vector<bool> subsumed(new_identifiers.size(), false);
      for(std::size_t i = 0; i < constraints.size(); ++i)
      {
        if(constraints[i].empty())
          continue;
        for(std::size_t j = 0; j < constraints.size(); ++j)
        {
          if(i == j || constraints[j].empty())
            continue;
          if(concept_subsumes(constraints[j], constraints[i]))
            subsumed[i] = true;
        }
      }

      resolve_identifierst filtered;
      auto it = new_identifiers.begin();
      for(std::size_t i = 0; i < new_identifiers.size(); ++i, ++it)
        if(!subsumed[i])
          filtered.push_back(*it);
      if(!filtered.empty() && filtered.size() < new_identifiers.size())
        new_identifiers = filtered;
    }

    {
      guess_function_template_args(new_identifiers, fargs);

      if(new_identifiers.empty())
      {
        new_identifiers = identifiers;
        // Template deduction failed for all templates, so remove them
        // to prevent raw template declarations from entering
        // disambiguate_functions.
        remove_templates(new_identifiers);
      }
    }

    disambiguate_functions(new_identifiers, fargs);

    // If template-instantiated candidates were all rejected by
    // disambiguate_functions, fall back to non-template overloads
    // which may match via implicit conversions.
    if(new_identifiers.empty())
    {
      new_identifiers = identifiers;
      remove_templates(new_identifiers);
      disambiguate_functions(new_identifiers, fargs);
    }

#ifdef DEBUG
    std::cout << "P3 " << base_name << " " << new_identifiers.size() << '\n';
    show_identifiers(base_name, new_identifiers, std::cout);
    std::cout << '\n';
#endif
  }
  else
    remove_duplicates(new_identifiers);

#ifdef DEBUG
  std::cout << "P4 " << base_name << " " << new_identifiers.size() << '\n';
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << '\n';
#endif

  if(new_identifiers.size() == 1)
  {
    result = *new_identifiers.begin();

    if(result.id() == ID_template_function_instance)
    {
      // template_function_instance should have been instantiated
      // by guess_function_template_args; if it wasn't, return nil
      // so the caller can try other resolution paths.
      if(!fail_with_exception)
        return nil_exprt();
    }
  }
  else
  {
    // nothing or too many
    if(!fail_with_exception)
      return nil_exprt();

    // When multiple candidates remain and no function arguments are
    // available for disambiguation (e.g., std::endl used as an
    // argument to operator<<), prefer the char-based instantiation
    // over wchar_t as a pragmatic default.
    bool resolved_by_filtering = false;
    if(new_identifiers.size() > 1 && !fargs.in_use)
    {
      resolve_identifierst filtered;
      for(const auto &id : new_identifiers)
      {
        const irep_idt &ident = id.get(ID_identifier);
        if(id2string(ident).find("wchar_t") == std::string::npos)
          filtered.push_back(id);
      }
      if(filtered.size() == 1)
      {
        result = filtered.front();
        resolved_by_filtering = true;
      }
    }

    if(!resolved_by_filtering)
    {
      if(new_identifiers.empty())
      {
        // Destructor overload resolution failure: return a dummy
        // destructor. Destructors are implicitly noexcept in C++11+.

        if(!base_name.empty() && id2string(base_name)[0] == '~')
        {
          exprt dtor{ID_symbol};
          dtor.type() = code_typet{{}, empty_typet{}};
          dtor.type().set(ID_destructor, true);
          dtor.add_source_location() = source_location;
          return dtor;
        }
        cpp_typecheck.error().source_location = source_location;
        cpp_typecheck.error() << "found no match for symbol '" << base_name
                              << "', candidates are:\n";
        show_identifiers(base_name, identifiers, cpp_typecheck.error());
      }
      else
      {
        cpp_typecheck.error().source_location = source_location;
        cpp_typecheck.error()
          << "symbol '" << base_name << "' does not uniquely resolve:\n";
        show_identifiers(base_name, new_identifiers, cpp_typecheck.error());

#ifdef DEBUG
        exprt e1 = *new_identifiers.begin();
        exprt e2 = *(++new_identifiers.begin());
        cpp_typecheck.error() << "e1==e2: " << (e1 == e2) << '\n';
        cpp_typecheck.error()
          << "e1.type==e2.type: " << (e1.type() == e2.type()) << '\n';
        cpp_typecheck.error()
          << "e1.id()==e2.id(): " << (e1.id() == e2.id()) << '\n';
        cpp_typecheck.error()
          << "e1.iden==e2.iden: "
          << (e1.get(ID_identifier) == e2.get(ID_identifier)) << '\n';
        cpp_typecheck.error() << "e1.iden:: " << e1.get(ID_identifier) << '\n';
        cpp_typecheck.error() << "e2.iden:: " << e2.get(ID_identifier) << '\n';
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
  }

  // we do some checks before we return

  // Access control check for class members resolved via qualified names.
  // The get_component path sets ID_C_not_accessible, but qualified name
  // resolution bypasses get_component, so we check here.
  // resolve_scope() changed the current scope to the target class, so we
  // must temporarily restore the original scope for check_component_access.
  if(
    !result.get_bool(ID_C_not_accessible) &&
    !cpp_typecheck.disable_access_control && original_scope != nullptr)
  {
    irep_idt result_id = result.get(ID_identifier);
    if(result_id.empty() && result.id() == ID_symbol)
      result_id = to_symbol_expr(result).get_identifier();

    if(!result_id.empty())
    {
      const std::string id_str = id2string(result_id);
      auto pos = id_str.rfind("::");
      if(pos != std::string::npos)
      {
        const std::string class_name = "tag-" + id_str.substr(0, pos);
        const symbolt *class_sym =
          cpp_typecheck.symbol_table.lookup(class_name);
        if(class_sym != nullptr && class_sym->type.id() == ID_struct)
        {
          const struct_typet &struct_type = to_struct_type(class_sym->type);
          for(const auto &comp : struct_type.components())
          {
            if(comp.get_name() == result_id)
            {
              // Temporarily restore the caller's scope for access check.
              cpp_scopet *saved = cpp_typecheck.cpp_scopes.current_scope_ptr;
              cpp_typecheck.cpp_scopes.current_scope_ptr = original_scope;
              bool not_ok =
                cpp_typecheck.check_component_access(comp, struct_type);
              cpp_typecheck.cpp_scopes.current_scope_ptr = saved;

              if(not_ok)
              {
                // If access check fails, silently mark as inaccessible
                // rather than throwing. This allows overload resolution
                // to proceed with other candidates (e.g., MSVC's
                // bad_alloc has a private const char* ctor alongside
                // the public default ctor).
                if(!fail_with_exception)
                  return nil_exprt();

                // Mark as inaccessible but don't throw — the caller
                // may have other overloads to try.
                result.set(ID_C_not_accessible, true);
                break;
              }
              break;
            }
          }
        }
      }
    }
  }

  if(result.get_bool(ID_C_not_accessible))
  {
    // Re-check access from the original (caller's) scope, since
    // resolve_scope() may have changed the current scope to the target
    // class, causing check_component_access to give a false positive.
    bool still_not_accessible = true;
    if(original_scope != nullptr)
    {
      irep_idt comp_name = result.get(ID_component_name);
      if(comp_name.empty())
      {
        comp_name = result.get(ID_identifier);
        if(comp_name.empty() && result.id() == ID_symbol)
          comp_name = to_symbol_expr(result).get_identifier();
      }

      if(!comp_name.empty())
      {
        const std::string id_str = id2string(comp_name);
        auto pos = id_str.rfind("::");
        if(pos != std::string::npos)
        {
          const std::string class_name = "tag-" + id_str.substr(0, pos);
          const symbolt *class_sym =
            cpp_typecheck.symbol_table.lookup(class_name);
          if(class_sym != nullptr && class_sym->type.id() == ID_struct)
          {
            const struct_typet &struct_type = to_struct_type(class_sym->type);
            for(const auto &comp : struct_type.components())
            {
              if(comp.get_name() == comp_name)
              {
                cpp_scopet *saved = cpp_typecheck.cpp_scopes.current_scope_ptr;
                cpp_typecheck.cpp_scopes.current_scope_ptr = original_scope;
                still_not_accessible =
                  cpp_typecheck.check_component_access(comp, struct_type);
                cpp_typecheck.cpp_scopes.current_scope_ptr = saved;
                break;
              }
            }
          }
        }
      }
    }

    if(still_not_accessible)
    {
      // Check if the caller is in a derived class — derived class
      // constructors can call base class constructors even if private
      // (e.g., MSVC's bad_array_new_length calling bad_alloc(const char*)).
      const irep_idt &current_class =
        cpp_typecheck.cpp_scopes.current_scope().get_parent().identifier;
      irep_idt comp_name = result.get(ID_component_name);
      if(!comp_name.empty() && !current_class.empty())
      {
        const std::string id_str = id2string(comp_name);
        auto pos = id_str.rfind("::");
        if(pos != std::string::npos)
        {
          const std::string base_class = "tag-" + id_str.substr(0, pos);
          // Check if current class inherits from the base class
          const symbolt *cur_sym =
            cpp_typecheck.symbol_table.lookup(current_class);
          if(cur_sym != nullptr && cur_sym->type.id() == ID_struct)
          {
            for(const auto &base : to_struct_type(cur_sym->type).bases())
            {
              if(
                base.type().id() == ID_struct_tag &&
                id2string(to_struct_tag_type(base.type()).get_identifier()) ==
                  base_class)
              {
                still_not_accessible = false;
                break;
              }
            }
          }
        }
      }
    }

    if(still_not_accessible)
    {
      // In system headers, silently ignore access violations —
      // they may result from incomplete modelling of friend
      // declarations or visibility attributes.
      const auto &loc = result.source_location();
      const std::string file = id2string(loc.get_file());
      if(
        !file.empty() && (file.find("/include/") != std::string::npos ||
                          file.find("\\include\\") != std::string::npos))
      {
        still_not_accessible = false;
      }
    }

    if(still_not_accessible)
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.error().source_location = result.source_location();
      cpp_typecheck.error() << "member '" << result.get(ID_component_name)
                            << "' is not accessible" << messaget::eom;
      throw 0;
    }
  }

  switch(want)
  {
  case wantt::VAR:
    if(result.id() == ID_type && !cpp_typecheck.cpp_is_pod(result.type()))
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.error().source_location = source_location;

      cpp_typecheck.error()
        << "expected expression, but got type '"
        << cpp_typecheck.to_string(result.type()) << "'" << messaget::eom;

      throw 0;
    }
    break;

  case wantt::TYPE:
    if(result.id() != ID_type)
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.error().source_location = source_location;

      cpp_typecheck.error()
        << "expected type, but got expression '"
        << cpp_typecheck.to_string(result) << "'" << messaget::eom;

      throw 0;
    }
    break;

  case wantt::BOTH:
    break;
  }

  return result;
}

void cpp_typecheck_resolvet::guess_template_args(
  const exprt &template_expr,
  const exprt &desired_expr)
{
  // An ambiguous node may contain a cpp_name that is a template parameter.
  // Extract the name for matching.
  const exprt &expr_to_match =
    template_expr.id() == ID_ambiguous
      ? static_cast<const exprt &>(
          static_cast<const irept &>(template_expr.type()))
      : template_expr;

  if(expr_to_match.id() == ID_cpp_name)
  {
    const cpp_namet &cpp_name = to_cpp_name(expr_to_match);

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
        if(id.id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
        {
          // see if unassigned
          exprt &e = cpp_typecheck.template_map.expr_map[id.identifier];
          if(e.id() == ID_unassigned)
          {
            e = desired_expr;
          }
        }
      }
    }
  }
}

/// Deduce template arguments by comparing a type pattern P against an
/// actual type A.  This implements [temp.deduct.type] from the C++ standard.
///
/// The type P (template_type) is composed from template parameters and
/// concrete types.  The type A (desired_type) is a fully resolved type.
/// The function attempts to find template argument values that make P
/// match A, recording them in the template_map.
///
/// Decomposition rules implemented (per [temp.deduct.type]/3):
///  - [temp.deduct.type]/8  reference types (is_reference branch)
///  - [temp.deduct.type]/9  pointer types (ID_pointer branch)
///  - [temp.deduct.type]/10 array types (ID_array branch)
///  - [temp.deduct.type]/11 function types (ID_code/ID_function_type branch)
///  - [temp.deduct.type]/3.3 class template specializations (cpp_name with
///    template_args — matches instantiation arguments
///    from ID_C_template_arguments)
///  - [temp.deduct.type]/14 cv-qualified types (ID_merged_type branch)
void cpp_typecheck_resolvet::guess_template_args(
  const typet &template_type,
  const typet &desired_type)
{
#ifdef DEBUG
  std::cout << "guess_template_args: TT.id=" << template_type.id()
            << " DT.id=" << desired_type.id() << '\n';
#endif

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

  if(template_type.id() == ID_cpp_name)
  {
    // we only care about cpp_names that are template parameters!
    const cpp_namet &cpp_name = to_cpp_name(template_type);

    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    if(cpp_name.has_template_args())
    {
      // Check if this is a template alias — if so, expand it and
      // re-try deduction with the underlying type pattern.
      {
        irep_idt base_name = cpp_name.get_base_name();
        const auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          base_name, cpp_scopet::RECURSIVE);
        for(const auto &id_ptr : id_set)
        {
          if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE)
          {
            const symbolt *sym =
              cpp_typecheck.symbol_table.lookup(id_ptr->identifier);
            if(
              sym != nullptr && sym->type.get_bool(ID_is_template) &&
              to_cpp_declaration(sym->type).is_template_alias())
            {
              // Get the alias's underlying type pattern
              const cpp_declarationt &alias_decl =
                to_cpp_declaration(sym->type);
              const cpp_declaratort &alias_declarator =
                alias_decl.declarators().front();
              typet alias_type = alias_declarator.merge_type(alias_decl.type());
              cpp_convert_plain_type(
                alias_type, cpp_typecheck.get_message_handler());

              // The alias template parameters map to the template
              // arguments in the cpp_name. Substitute them.
              const auto &alias_params =
                alias_decl.template_type().template_parameters();
              const auto &name_args = cpp_name.get_sub().back();
              const irept::subt &targs = name_args.find(ID_arguments).get_sub();

              // Build a substitution from alias params to the
              // template arguments (which are themselves template
              // parameters of the enclosing function template).
              // For each alias param, find the corresponding targ
              // and substitute in alias_type.
              for(std::size_t i = 0;
                  i < alias_params.size() && i < targs.size();
                  ++i)
              {
                // The targ is a cpp_name referencing the function
                // template's parameter. We need to substitute the
                // alias param name in alias_type with this cpp_name.
                const irept &targ = targs[i];
                const irept &targ_type =
                  targ.id() == ID_ambiguous ? targ.find(ID_type) : targ;
                if(targ_type.id() != ID_cpp_name)
                  continue;

                // Find the alias param name in alias_type and replace
                std::function<void(irept &)> subst;
                subst = [&](irept &t)
                {
                  if(t.id() == ID_cpp_name)
                  {
                    const cpp_namet &n =
                      to_cpp_name(static_cast<const typet &>(t));
                    if(
                      !n.is_qualified() && !n.has_template_args() &&
                      n.get_base_name() == alias_params[i].get(ID_C_base_name))
                    {
                      t = targ_type;
                      return;
                    }
                  }
                  for(auto &sub : t.get_sub())
                    subst(sub);
                  for(auto &ns : t.get_named_sub())
                    subst(ns.second);
                };
                subst(static_cast<irept &>(alias_type));
              }

              // Now deduce with the expanded alias type
              guess_template_args(alias_type, desired_type);
              return;
            }
          }
        }
      }

      // This could be something like my_template<T>, and we need
      // to match 'T'. Then 'desired_type' has to be a template instance.

      const auto &name_args = cpp_name.get_sub().back();
      if(name_args.id() != ID_template_args)
        return;

      const irept::subt &targs = name_args.find(ID_arguments).get_sub();

      // Helper: when deduction for C<T> fails (desired type is not an
      // instantiation of C), mark any template parameters in targs
      // as deduction-failed. This uses ID_nil as a poison value that
      // prevents later assignment from other parameters and causes
      // has_unassigned() to fail (since ID_nil != any valid type).
      auto mark_targs_conflicting = [&]()
      {
        for(const auto &targ : targs)
        {
          const irept &t =
            targ.id() == ID_ambiguous ? targ.find(ID_type) : targ;
          if(t.id() != ID_cpp_name)
            continue;
          const cpp_namet &tn = to_cpp_name(static_cast<const typet &>(t));
          if(tn.is_qualified() || tn.has_template_args())
            continue;
          irep_idt bname = tn.get_base_name();
          const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
            bname, cpp_scopet::RECURSIVE);
          for(const auto &id_ptr : ids)
          {
            if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
            {
              auto it =
                cpp_typecheck.template_map.type_map.find(id_ptr->identifier);
              if(it != cpp_typecheck.template_map.type_map.end())
              {
                // Mark as deduction-failed using ID_nil.
                // This prevents later assignment from other parameters
                // (the simple T case checks for ID_unassigned, and
                // ID_nil != ID_unassigned).
                it->second = typet(ID_nil);
              }
            }
          }
        }
      };

      // desired_type must be a struct/union tag that was instantiated
      // from a template
      irep_idt desired_id;
      if(desired_type.id() == ID_struct_tag)
        desired_id = to_struct_tag_type(desired_type).get_identifier();
      else if(desired_type.id() == ID_union_tag)
        desired_id = to_union_tag_type(desired_type).get_identifier();
      else
      {
        mark_targs_conflicting();
        return;
      }

      const symbolt *desired_sym =
        cpp_typecheck.symbol_table.lookup(desired_id);
      if(desired_sym == nullptr)
      {
        mark_targs_conflicting();
        return;
      }

      // Check if it was instantiated from a template
      if(desired_sym->type.find(ID_C_template).is_nil())
      {
        mark_targs_conflicting();
        return;
      }

      // Verify that the template name in the cpp_name matches the
      // template the desired type was instantiated from. Without this
      // check, template argument deduction would incorrectly match
      // unrelated template instantiations (e.g., deducing I=char from
      // move_iterator<I> when the argument is basic_string<char>).
      {
        irep_idt tmpl_base_name = cpp_name.get_base_name();
        if(!tmpl_base_name.empty() && tmpl_base_name != desired_sym->base_name)
        {
          // Check if the template name is a template template parameter.
          // If so, assign it to the desired type's template.
          bool is_tt_param = false;
          const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
            tmpl_base_name, cpp_scopet::RECURSIVE);
          for(const auto &id_ptr : ids)
          {
            if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
            {
              auto it =
                cpp_typecheck.template_map.type_map.find(id_ptr->identifier);
              if(
                it != cpp_typecheck.template_map.type_map.end() &&
                it->second.id() == ID_unassigned)
              {
                // Assign the template template parameter to the
                // template that the desired type was instantiated from.
                it->second = desired_type;
                is_tt_param = true;
              }
            }
          }
          if(!is_tt_param)
          {
            mark_targs_conflicting();
            return;
          }
        }
      }
      const irept &inst_args = desired_sym->type.find(ID_C_template_arguments);
      if(inst_args.is_nil())
      {
        mark_targs_conflicting();
        return;
      }

      const auto &inst_arguments =
        static_cast<const cpp_template_args_tct &>(inst_args).arguments();

      // Match each template arg from the cpp_name against the
      // corresponding instantiation arg
      for(std::size_t i = 0; i < targs.size() && i < inst_arguments.size(); i++)
      {
        if(inst_arguments[i].id() == ID_type)
        {
          // The targ might be an "ambiguous" node with a type sub
          const typet &targ_type =
            targs[i].id() == ID_ambiguous
              ? static_cast<const typet &>(targs[i].find(ID_type))
              : static_cast<const typet &>(
                  static_cast<const irept &>(targs[i]));
          guess_template_args(targ_type, inst_arguments[i].type());
        }
        else
        {
          guess_template_args(
            static_cast<const exprt &>(targs[i]), inst_arguments[i]);
        }
      }
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
          if(id.id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
          {
            // see if unassigned
            typet &t = cpp_typecheck.template_map.type_map[id.identifier];
            if(t.id() == ID_unassigned)
            {
              t = desired_type;
            }
            else
            {
              // Already assigned — check for conflict.
              // Strip cv-qualifiers for comparison.
              typet existing = t;
              typet incoming = desired_type;
              existing.remove(ID_C_constant);
              existing.remove(ID_C_volatile);
              incoming.remove(ID_C_constant);
              incoming.remove(ID_C_volatile);
              if(existing != incoming)
                t.id(ID_unassigned); // mark as conflicting
            }
          }
        }
      }
    }
  }
  else if(template_type.id() == ID_merged_type)
  {
    // Strip cv-qualifiers from the desired type when the merged_type
    // contains them, so that e.g. const T matched against const char
    // deduces T=char rather than T=const char.
    typet desired = desired_type;
    for(const auto &t : to_merged_type(template_type).subtypes())
    {
      if(t.id() == ID_const)
        desired.remove(ID_C_constant);
      else if(t.id() == ID_volatile)
        desired.remove(ID_C_volatile);
      else
        guess_template_args(t, desired);
    }
  }
  // [temp.deduct.type]/14: cv-qualified types — strip cv and recurse
  else if(is_reference(template_type) || is_rvalue_reference(template_type))
  {
    // [temp.deduct.type]/8: if P is a reference type, the referred-to
    // type is used for type deduction.
    typet desired = desired_type;
    if(is_reference(desired) || is_rvalue_reference(desired))
      desired = to_reference_type(desired).base_type();
    guess_template_args(to_reference_type(template_type).base_type(), desired);
  }
  else if(template_type.id() == ID_pointer)
  {
    if(desired_type.id() == ID_pointer)
      guess_template_args(
        to_pointer_type(template_type).base_type(),
        to_pointer_type(desired_type).base_type());
  }
  else if(template_type.id() == ID_frontend_pointer)
  {
    if(desired_type.id() == ID_pointer)
      guess_template_args(
        to_type_with_subtype(template_type).subtype(),
        to_pointer_type(desired_type).base_type());
  }
  else if(template_type.id() == ID_array)
  {
    if(desired_type.id() == ID_array)
    {
      // look at subtype first
      guess_template_args(
        to_array_type(template_type).element_type(),
        to_array_type(desired_type).element_type());

      // size (e.g., buffer size guessing)
      guess_template_args(
        to_array_type(template_type).size(),
        to_array_type(desired_type).size());
    }
  }
  else if(template_type.id() == ID_function_type)
  {
    // function_type is the pre-conversion form of code type.
    // Match return type and parameter types.
    if(desired_type.id() == ID_code)
    {
      const code_typet &desired_code = to_code_type(desired_type);

      // Match return type (stored as subtype in function_type)
      if(template_type.has_subtype())
      {
        guess_template_args(
          to_type_with_subtype(template_type).subtype(),
          desired_code.return_type());
      }

      // Match parameter types
      const irept::subt &tmpl_params =
        template_type.find(ID_parameters).get_sub();
      const code_typet::parameterst &desired_params = desired_code.parameters();

      auto d_it = desired_params.begin();
      for(const auto &tp : tmpl_params)
      {
        if(tp.id() == ID_ellipsis)
          break;
        if(d_it == desired_params.end())
          break;

        if(tp.id() == ID_cpp_declaration)
        {
          const cpp_declarationt &decl = to_cpp_declaration(tp);
          if(!decl.declarators().empty())
          {
            try
            {
              typet param_type =
                decl.declarators().front().merge_type(decl.type());
              cpp_convert_plain_type(
                param_type, cpp_typecheck.get_message_handler());
              guess_template_args(param_type, d_it->type());
            }
            catch(...)
            {
              // ignore conversion errors
            }
          }
        }

        ++d_it;
      }
    }
  }
  else if(template_type.id() == ID_code)
  {
    // Both template and desired are already-converted code types.
    if(desired_type.id() == ID_code)
    {
      const code_typet &tmpl_code = to_code_type(template_type);
      const code_typet &desired_code = to_code_type(desired_type);

      guess_template_args(tmpl_code.return_type(), desired_code.return_type());

      const auto &tmpl_params = tmpl_code.parameters();
      const auto &desired_params = desired_code.parameters();
      auto d_it = desired_params.begin();
      for(const auto &tp : tmpl_params)
      {
        if(d_it == desired_params.end())
          break;
        guess_template_args(tp.type(), d_it->type());
        ++d_it;
      }
    }
  }
}

/// Deduce template arguments for a function template from a function call.
///
/// Implements [temp.deduct.call]: for each function template parameter type P
/// that contains template parameters, compare P with the type of the
/// corresponding call argument A.  Also implements [temp.deduct.funcaddr]
/// when called with synthetic fargs from known class template instantiations.
///
/// Key rules implemented:
///  - [temp.deduct.call]/1: P/A comparison for each parameter
///  - [temp.deduct.call]/3: forwarding references (T&& with lvalue → T&)
///  - [temp.deduct.call]/4: cv-stripping when P is just T (not T&, T*, etc.)
///  - [temp.deduct.call]/4: array-to-pointer decay
///  - [temp.deduct.funcaddr]: deduction from function address target type
exprt cpp_typecheck_resolvet::guess_function_template_args(
  const exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  const typet &tmp =
    expr.type().id() == ID_struct_tag
      ? static_cast<const typet &>(
          cpp_typecheck.follow_tag(to_struct_tag_type(expr.type())))
    : expr.type().id() == ID_union_tag
      ? static_cast<const typet &>(
          cpp_typecheck.follow_tag(to_union_tag_type(expr.type())))
    : expr.type().id() == ID_c_enum_tag
      ? static_cast<const typet &>(
          cpp_typecheck.follow_tag(to_c_enum_tag_type(expr.type())))
      : expr.type();

  if(!tmp.get_bool(ID_is_template))
    return nil_exprt(); // not a template

  PRECONDITION(expr.id() == ID_symbol);

  // a template is always a declaration
  const cpp_declarationt &cpp_declaration = to_cpp_declaration(tmp);

  // Class templates require explicit template arguments,
  // no guessing!
  if(cpp_declaration.is_class_template())
    return nil_exprt();

  // we need function arguments for guessing
  if(fargs.operands.empty() && expr.find(ID_C_template_arguments).is_nil())
  {
    // C++11: check if all template parameters have default values
    const auto &params = cpp_declaration.template_type().template_parameters();
    bool all_have_defaults = !params.empty();
    for(const auto &p : params)
    {
      if(p.find(ID_C_default_value).is_nil())
      {
        all_have_defaults = false;
        break;
      }
    }
    if(!all_have_defaults)
    {
      // [temp.deduct.funcaddr]: try to deduce template arguments
      // from the function's parameter types by matching against
      // known class template instantiations in the symbol table.
      // Build synthetic fargs from the instantiation types and
      // let the existing deduction code handle the matching.
      bool deduced_from_context = false;
      if(
        cpp_declaration.declarators().size() == 1 &&
        cpp_declaration.declarators()[0].type().id() == ID_function_type)
      {
        const auto &fn_params =
          cpp_declaration.declarators()[0].type().find(ID_parameters);
        for(const auto &param : fn_params.get_sub())
        {
          if(param.id() != ID_cpp_declaration)
            continue;
          const auto &pdecl =
            to_cpp_declaration(static_cast<const exprt &>(param));
          if(pdecl.declarators().empty())
            continue;
          typet ptype = pdecl.declarators()[0].merge_type(pdecl.type());
          // Strip reference
          bool is_ref = false;
          if(ptype.id() == ID_frontend_pointer || ptype.id() == ID_pointer)
          {
            if(!ptype.get_sub().empty())
              ptype = static_cast<const typet &>(ptype.get_sub()[0]);
            is_ref = true;
          }
          if(ptype.id() != ID_cpp_name)
            continue;
          irep_idt base = to_cpp_name(ptype).get_base_name();
          if(base.empty())
            continue;
          // Search for a complete instantiation
          std::string search = "tag-" + id2string(base) + "<";
          for(const auto &entry : cpp_typecheck.symbol_table.symbols)
          {
            const std::string &eid = id2string(entry.first);
            if(eid.find(search) == std::string::npos)
              continue;
            // Skip virtual tables and other non-type symbols
            if(eid.find("virtual_table") != std::string::npos)
              continue;
            if(
              entry.second.type.id() != ID_struct ||
              to_struct_type(entry.second.type).is_incomplete())
              continue;
            // Build a synthetic fargs with this instantiation type
            // and re-call guess_function_template_args
            typet arg_type{struct_tag_typet{entry.first}};
            if(is_ref)
              arg_type = reference_type(arg_type);
            symbol_exprt synthetic{"funcaddr_synthetic", arg_type};
            cpp_typecheck_fargst synthetic_fargs;
            synthetic_fargs.operands.push_back(synthetic);
            exprt result;
            try
            {
              result = guess_function_template_args(expr, synthetic_fargs);
            }
            catch(...)
            {
              continue;
            }
            if(result.is_not_nil())
            {
              deduced_from_context = true;
              return result;
            }
          }
          break; // only try the first parameter
        }
      }
      if(!deduced_from_context)
        return nil_exprt(); // give up
    }
  }

  // We need to guess in the case of function templates!

  irep_idt template_identifier = to_symbol_expr(expr).get_identifier();

  const symbolt &template_symbol = cpp_typecheck.lookup(template_identifier);

  // alright, set up template arguments as 'unassigned'

  cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);

  cpp_typecheck.template_map.build_unassigned(cpp_declaration.template_type());

  // If this is a template constructor inside an instantiated template class,
  // pre-populate the template map with the class template arguments so that
  // class template parameters (e.g., Alloc) are resolved.
  {
    irep_idt class_tag = expr.get(ID_C_class);

    // If ID_C_class is not set, try to derive it from the template
    // identifier for template constructors. Template constructors
    // inside class templates have identifiers like
    // "ClassName::template.CtorName<...>()->(constructor)".
    // Only do this for constructors — member function templates have
    // their own independent template parameters.
    if(class_tag.empty() && cpp_declaration.is_constructor())
    {
      const std::string &tid = id2string(template_identifier);
      auto pos = tid.find("::template.");
      if(pos != std::string::npos)
      {
        class_tag = "tag-" + tid.substr(0, pos);
      }
    }

    if(!class_tag.empty())
    {
      const symbolt *class_sym = cpp_typecheck.symbol_table.lookup(class_tag);
      if(
        class_sym != nullptr &&
        class_sym->type.find(ID_C_template).is_not_nil() &&
        class_sym->type.find(ID_C_template_arguments).is_not_nil())
      {
        cpp_typecheck.template_map.build(
          static_cast<const template_typet &>(
            class_sym->type.find(ID_C_template)),
          static_cast<const cpp_template_args_tct &>(
            class_sym->type.find(ID_C_template_arguments)));
      }
    }
  }

  // If explicit template arguments were provided (partial explicit args),
  // pre-populate the template map with them before deduction.
  const irept &stored_args = expr.find(ID_C_template_arguments);
  if(stored_args.is_not_nil())
  {
    const cpp_template_args_tct &explicit_args =
      to_cpp_template_args_tc(stored_args);
    const auto &params = cpp_declaration.template_type().template_parameters();
    for(std::size_t i = 0;
        i < explicit_args.arguments().size() && i < params.size();
        i++)
    {
      if(
        explicit_args.arguments()[i].id() != ID_unassigned &&
        explicit_args.arguments()[i].type().id() != ID_unassigned)
      {
        cpp_typecheck.template_map.set(params[i], explicit_args.arguments()[i]);
      }
    }
  }

  // there should be exactly one declarator
  PRECONDITION(cpp_declaration.declarators().size() == 1);

  const cpp_declaratort &function_declarator =
    cpp_declaration.declarators().front();

  // and that needs to have function type
  if(function_declarator.type().id() != ID_function_type)
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "expected function type for function template"
                          << messaget::eom;
    throw 0;
  }

  cpp_save_scopet cpp_saved_scope(cpp_typecheck.cpp_scopes);

  // we need the template scope
  cpp_scopet *template_scope = static_cast<cpp_scopet *>(
    cpp_typecheck.cpp_scopes.id_map[template_identifier]);

  if(template_scope == nullptr)
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template identifier: " << template_identifier
                          << '\n'
                          << "function template instantiation error"
                          << messaget::eom;
    throw 0;
  }

  // enter the scope of the template
  cpp_typecheck.cpp_scopes.go_to(*template_scope);

  // walk through the function parameters
  const irept::subt &parameters =
    function_declarator.type().find(ID_parameters).get_sub();

  exprt::operandst::const_iterator it = fargs.operands.begin();

  // Skip the implicit 'this' object argument for member functions.
  if(fargs.has_object && it != fargs.operands.end())
    ++it;

  // Track pack expansion size for non-empty packs
  std::size_t pack_expansion_size = 0;
  bool has_non_empty_pack = false;
  std::vector<typet> pack_deduced_types;

  for(const auto &parameter : parameters)
  {
    if(it == fargs.operands.end())
      break;

    if(parameter.id() == ID_cpp_declaration)
    {
      const cpp_declarationt &arg_declaration = to_cpp_declaration(parameter);

      // again, there should be one declarator
      DATA_INVARIANT(
        arg_declaration.declarators().size() == 1, "exactly one declarator");

      const cpp_declaratort &declarator = arg_declaration.declarators().front();

      // Check if this is a parameter pack (e.g., Args... args)
      bool is_pack = declarator.get_bool(ID_ellipsis) ||
                     declarator.type().get_bool(ID_ellipsis);

      // turn into type
      typet arg_type = declarator.merge_type(arg_declaration.type());

      // We only convert the arg_type,
      // and don't typecheck it -- that could cause all
      // sorts of trouble.
      cpp_convert_plain_type(arg_type, cpp_typecheck.get_message_handler());

      // For pack parameters, deduce from all remaining arguments
      if(is_pack)
      {
        pack_expansion_size =
          static_cast<std::size_t>(fargs.operands.end() - it);
        has_non_empty_pack = pack_expansion_size > 0;
        // Collect each argument's type for heterogeneous packs
        for(; it != fargs.operands.end(); ++it)
        {
          typet arg_actual_type = it->type();
          if(arg_type.id() == ID_cpp_name)
          {
            arg_actual_type.remove(ID_C_constant);
            arg_actual_type.remove(ID_C_volatile);
            if(arg_actual_type.id() == ID_array)
              arg_actual_type =
                pointer_type(to_array_type(arg_actual_type).element_type());
          }
          pack_deduced_types.push_back(arg_actual_type);
          guess_template_args(arg_type, arg_actual_type);
        }
        continue;
      }

      // [temp.deduct.call]/3: forwarding reference — if the parameter is
      // T&& where T is a template parameter, and the argument is an
      // lvalue, deduce T as "lvalue reference to A".
      // Exception: a dereference of an rvalue reference (e.g., the
      // result of std::move) is an xvalue, not an lvalue.
      // Named rvalue reference variables are lvalues, not xvalues.
      bool is_lvalue = it->get_bool(ID_C_lvalue);
      if(
        is_lvalue && it->id() == ID_dereference && it->operands().size() == 1 &&
        it->operands().front().type().id() == ID_pointer &&
        it->operands().front().type().get_bool(ID_C_rvalue_reference) &&
        it->operands().front().id() != ID_symbol)
      {
        is_lvalue = false;
      }
      if(
        is_rvalue_reference(arg_type) && is_lvalue &&
        to_pointer_type(arg_type).base_type().id() == ID_cpp_name)
      {
        typet lvalue_ref_type = ::reference_type(it->type());
        guess_template_args(
          to_pointer_type(arg_type).base_type(), lvalue_ref_type);
      }
      else
      {
        // [temp.deduct.call]/4: when P is just T (not T&, T*, etc.),
        // top-level cv-qualifiers on A are ignored.
        // Also, array types decay to pointer types per [temp.deduct.call]/4.
        typet arg_actual_type = it->type();
        if(arg_type.id() == ID_cpp_name)
        {
          arg_actual_type.remove(ID_C_constant);
          arg_actual_type.remove(ID_C_volatile);
          if(arg_actual_type.id() == ID_array)
            arg_actual_type =
              pointer_type(to_array_type(arg_actual_type).element_type());
        }
        guess_template_args(arg_type, arg_actual_type);
      }
    }

    ++it;
  }

  // see if that has worked out

  cpp_template_args_tct template_args =
    cpp_typecheck.template_map.build_template_args(
      cpp_declaration.template_type());

  // For non-empty variadic packs, expand the single deduced pack type
  // to N copies in the template args so that template instantiation
  // sees the correct number of arguments.
  if(has_non_empty_pack && pack_expansion_size > 1)
  {
    const auto &params = cpp_declaration.template_type().template_parameters();
    auto &args = template_args.arguments();
    // Find the pack parameter (last one with ellipsis)
    for(std::size_t i = 0; i < params.size() && i < args.size(); ++i)
    {
      if(params[i].get_bool(ID_ellipsis))
      {
        // Use individually deduced types for heterogeneous packs
        if(pack_deduced_types.size() == pack_expansion_size)
        {
          // Replace the single deduced type with the first, then
          // insert the rest
          args[i] = exprt(ID_type);
          args[i].type() = pack_deduced_types[0];
          for(std::size_t j = 1; j < pack_expansion_size; ++j)
          {
            exprt arg(ID_type);
            arg.type() = pack_deduced_types[j];
            args.insert(args.begin() + i + j, arg);
          }
        }
        else
        {
          // Fallback: duplicate the single deduced type
          exprt pack_arg = args[i];
          for(std::size_t j = 1; j < pack_expansion_size; ++j)
            args.insert(args.begin() + i + j, pack_arg);
        }
        break;
      }
    }
  }

  // Convert deduction-failed markers (ID_nil) to ID_unassigned so that
  // has_unassigned() detects them and rejects the template.
  for(auto &arg : template_args.arguments())
  {
    if(arg.type().id() == ID_nil)
      arg.type().id(ID_unassigned);
  }

  // Apply default template arguments for any remaining unassigned parameters.
  // For example, template<typename T, typename R = T, ...> where R is not
  // deducible from function parameters but has a default value.
  // Also handle variadic packs with zero arguments.
  bool variadic_pack_empty = false;
  irep_idt pack_param_name;
  if(template_args.has_unassigned())
  {
    const auto &params = cpp_declaration.template_type().template_parameters();
    auto &args = template_args.arguments();

    for(std::size_t i = 0; i < args.size() && i < params.size(); i++)
    {
      if(args[i].id() == ID_unassigned || args[i].type().id() == ID_unassigned)
      {
        const template_parametert &param =
          static_cast<const template_parametert &>(params[i]);

        // Variadic pack with zero arguments: truncate args here.
        if(param.get_bool(ID_ellipsis))
        {
          const std::string full_id =
            id2string(param.type().get(ID_identifier));
          auto pos = full_id.rfind("::");
          pack_param_name =
            pos != std::string::npos ? full_id.substr(pos + 2) : full_id;
          args.resize(i);
          variadic_pack_empty = true;
          break;
        }

        if(param.has_default_argument() && param.id() == ID_type)
        {
          typet default_type = param.default_argument().type();
          // Evaluate the default argument in a SFINAE context: suppress
          // error messages and treat failure as deduction failure.
          null_message_handlert null_handler;
          message_handlert &old_handler = cpp_typecheck.get_message_handler();
          cpp_typecheck.set_message_handler(null_handler);
          try
          {
            cpp_save_scopet saved_scope(cpp_typecheck.cpp_scopes);
            cpp_idt *tscope =
              cpp_typecheck.cpp_scopes.id_map[template_symbol.name];
            if(tscope != nullptr)
              cpp_typecheck.cpp_scopes.go_to(*tscope);
            cpp_typecheck.typecheck_type(default_type);
            cpp_typecheck.template_map.apply(default_type);
            args[i] = exprt(ID_type);
            args[i].type() = default_type;
            cpp_typecheck.template_map.set(param, args[i]);
            cpp_typecheck.set_message_handler(old_handler);
          }
          catch(...)
          {
            cpp_typecheck.set_message_handler(old_handler);
            // If this is an anonymous type parameter, the default
            // argument is a SFINAE constraint (e.g.,
            // typename = enable_if_t<...>).
            const irep_idt &param_id = param.type().get(ID_identifier);
            bool is_anonymous = param_id.empty();
            if(!is_anonymous)
            {
              const std::string pid = id2string(param_id);
              auto pos = pid.rfind("::");
              const std::string local =
                pos != std::string::npos ? pid.substr(pos + 2) : pid;
              is_anonymous = local.empty() || local.find("anon") == 0;
            }
            if(is_anonymous)
            {
              // SFINAE constraint evaluation failed — reject the
              // template (substitution failure is not an error).
              return nil_exprt();
            }
          }
        }
        else if(param.has_default_argument() && param.id() != ID_type)
        {
          // Non-type parameter with default value (e.g.,
          // typename enable_if<...>::type = 0).
          // Evaluate the parameter type in a SFINAE context.
          null_message_handlert null_handler;
          message_handlert &old_handler = cpp_typecheck.get_message_handler();
          cpp_typecheck.set_message_handler(null_handler);
          try
          {
            // [temp.point] p1,7: the context of a template instantiation
            // includes both the definition and instantiation contexts.
            // Use the current (instantiation) scope rather than the
            // template (definition) scope, because the template scope
            // may lack using-scope links to enclosing inline namespaces
            // (e.g., std::__1 in libc++). The instantiation scope has
            // full visibility of the enclosing namespace.
            typet param_type = param.type();
            cpp_typecheck.template_map.apply(param_type);
            cpp_typecheck.typecheck_type(param_type);
            // Use the default value
            exprt default_val = param.default_argument();
            cpp_typecheck.template_map.apply(default_val);
            cpp_typecheck.typecheck_expr(default_val);
            args[i] = default_val;
            cpp_typecheck.template_map.set(param, args[i]);
            cpp_typecheck.set_message_handler(old_handler);
          }
          catch(...)
          {
            cpp_typecheck.set_message_handler(old_handler);
            // SFINAE: substitution failure in parameter type
            return nil_exprt();
          }
        }
      }
    }
  }

  if(template_args.has_unassigned())
    return nil_exprt(); // give up

  // Build the type of the function.

  typet function_type = function_declarator.merge_type(cpp_declaration.type());

  // When a variadic pack is empty, remove pack-expanded parameters from
  // the function type before typechecking, since the pack type name
  // (e.g. Base) has no mapping in the template map.
  if(variadic_pack_empty && function_type.id() == ID_function_type)
  {
    irept::subt &params = function_type.add(ID_parameters).get_sub();
    // Remove parameters whose declarator has ellipsis (the pack parameter)
    params.erase(
      std::remove_if(
        params.begin(),
        params.end(),
        [](const irept &p)
        {
          if(p.id() == ID_cpp_declaration)
          {
            const auto &decl = to_cpp_declaration(p);
            if(!decl.declarators().empty())
            {
              const auto &d = decl.declarators().front();
              return d.get_bool(ID_ellipsis) || d.type().get_bool(ID_ellipsis);
            }
          }
          return p.id() == ID_ellipsis;
        }),
      params.end());
    // Also strip ellipsis and pack parameter from nested function pointer types
    for(auto &p : params)
    {
      if(p.id() == ID_cpp_declaration)
      {
        auto &decl = to_cpp_declaration(p);
        if(!decl.declarators().empty())
        {
          irept &dtype = decl.declarators().front().type();
          if(dtype.id() == ID_frontend_pointer)
          {
            if(
              !dtype.get_sub().empty() &&
              dtype.get_sub().front().id() == ID_function_type)
            {
              irept::subt &inner_params =
                dtype.get_sub().front().add(ID_parameters).get_sub();
              inner_params.erase(
                std::remove_if(
                  inner_params.begin(),
                  inner_params.end(),
                  [&pack_param_name](const irept &ip)
                  {
                    if(ip.id() == ID_ellipsis)
                      return true;
                    if(ip.id() == ID_cpp_declaration)
                    {
                      const auto &d = to_cpp_declaration(ip);
                      if(d.type().id() == ID_cpp_name)
                      {
                        for(const auto &sub : d.type().get_sub())
                        {
                          if(
                            sub.id() == ID_name &&
                            sub.get(ID_identifier) == pack_param_name)
                            return true;
                        }
                      }
                    }
                    return false;
                  }),
                inner_params.end());
            }
          }
        }
      }
    }
  }

  // When a variadic pack is non-empty, expand the pack parameter to
  // N copies in the function type so that it matches the argument count.
  if(has_non_empty_pack && function_type.id() == ID_function_type)
  {
    irept::subt &fparams = function_type.add(ID_parameters).get_sub();
    irept::subt expanded;
    for(const auto &p : fparams)
    {
      bool is_pack_param = false;
      if(p.id() == ID_cpp_declaration)
      {
        const auto &decl = to_cpp_declaration(p);
        if(!decl.declarators().empty())
        {
          const auto &d = decl.declarators().front();
          is_pack_param =
            d.get_bool(ID_ellipsis) || d.type().get_bool(ID_ellipsis);
        }
      }
      else if(p.id() == ID_ellipsis)
      {
        is_pack_param = true;
      }

      if(is_pack_param)
      {
        // Create N copies of the pack parameter without the ellipsis flag
        for(std::size_t i = 0; i < pack_expansion_size; ++i)
        {
          if(p.id() == ID_cpp_declaration)
          {
            irept copy = p;
            auto &decl = static_cast<cpp_declarationt &>(copy);
            if(!decl.declarators().empty())
            {
              auto &d = decl.declarators().front();
              d.set(ID_ellipsis, false);
              d.type().set(ID_ellipsis, false);
            }
            // For heterogeneous packs, set the type from the
            // individually deduced types
            if(i < pack_deduced_types.size())
              decl.type() = pack_deduced_types[i];
            expanded.push_back(std::move(copy));
          }
        }
      }
      else
      {
        expanded.push_back(p);
      }
    }
    fparams = std::move(expanded);
  }

  // Type-check the function type in a SFINAE context: suppress error
  // messages so that substitution failures (e.g., enable_if with false
  // condition in the return type) are silently discarded.
  null_message_handlert null_handler;
  message_handlert &old_handler = cpp_typecheck.get_message_handler();
  try
  {
    cpp_typecheck.set_message_handler(null_handler);
    // Apply template map to the function type before typechecking.
    // This handles template template parameters where C<T> in the
    // function type needs to be replaced with the actual instantiated type.
    cpp_typecheck.template_map.apply(function_type);
    // Also apply to parameters stored as cpp_declarations
    if(function_type.id() == ID_function_type)
    {
      irept::subt &params = function_type.add(ID_parameters).get_sub();
      for(auto &p : params)
      {
        if(p.id() == ID_cpp_declaration)
        {
          auto &decl = static_cast<cpp_declarationt &>(p);
          cpp_typecheck.template_map.apply(decl.type());
        }
      }

      // For trailing return types with decltype referencing parameters,
      // put function parameters temporarily into scope.
      if(
        function_type.has_subtype() &&
        to_type_with_subtype(function_type).subtype().id() == ID_decltype)
      {
        for(const auto &p : params)
        {
          if(p.id() != ID_cpp_declaration)
            continue;
          const auto &pdecl = static_cast<const cpp_declarationt &>(p);
          if(pdecl.declarators().empty())
            continue;
          typet ptype = pdecl.type();
          cpp_typecheck.typecheck_type(ptype);
          const auto &pname_sub = pdecl.declarators().front().name().get_sub();
          if(pname_sub.empty())
            continue;
          const irep_idt &pname = pname_sub.front().get(ID_identifier);
          if(pname.empty())
            continue;
          const std::string sym_name =
            id2string(cpp_typecheck.cpp_scopes.current_scope().prefix) +
            id2string(pname);
          if(!cpp_typecheck.symbol_table.has_symbol(sym_name))
          {
            auxiliary_symbolt psym;
            psym.name = sym_name;
            psym.base_name = pname;
            psym.type = ptype;
            psym.mode = ID_cpp;
            psym.is_parameter = true;
            cpp_typecheck.symbol_table.insert(std::move(psym));
            const symbolt &inserted =
              cpp_typecheck.symbol_table.lookup_ref(sym_name);
            cpp_idt &id = cpp_typecheck.cpp_scopes.put_into_scope(inserted);
            id.id_class = cpp_idt::id_classt::SYMBOL;
          }
        }
      }
    }
    cpp_typecheck.typecheck_type(function_type);
    cpp_typecheck.set_message_handler(old_handler);
  }
  catch(...)
  {
    cpp_typecheck.set_message_handler(old_handler);
    return nil_exprt();
  }

  // Apply the template map to default values in the function parameters,
  // so that unresolved template parameter names (e.g., Alloc()) are
  // substituted before the function type is used for disambiguation.
  if(function_type.id() == ID_code)
  {
    for(auto &param : to_code_type(function_type).parameters())
    {
      if(param.default_value().is_not_nil())
        cpp_typecheck.template_map.apply(param.default_value());
    }
  }

  // When a variadic template parameter pack (e.g., Base...) appears in a
  // function pointer parameter type like T(*)(const C*, C**, Base...),
  // the pack expansion produces an ellipsis node that gets converted to
  // a C-style ellipsis by read_function_type. After template substitution,
  // the pack is expanded to concrete types, so the ellipsis must be removed
  // from nested function pointer types.
  if(function_type.id() == ID_code)
  {
    bool has_variadic_pack = false;
    for(const auto &p : cpp_declaration.template_type().template_parameters())
    {
      if(p.get_bool(ID_ellipsis))
      {
        has_variadic_pack = true;
        break;
      }
    }

    if(has_variadic_pack)
    {
      for(auto &param : to_code_type(function_type).parameters())
      {
        if(param.type().id() == ID_pointer)
        {
          typet &base = to_pointer_type(param.type()).base_type();
          if(base.id() == ID_code)
          {
            code_typet &ct = to_code_type(base);
            if(ct.has_ellipsis())
              ct.remove_ellipsis();
          }
        }
      }
    }
  }

  // Remember that this was a template

  function_type.set(ID_C_template, template_symbol.name);
  function_type.set(ID_C_template_arguments, template_args);

  // Propagate the class tag for template constructors in instantiated
  // template classes, so that instantiate_template can build the class
  // template map.
  const irep_idt &class_tag = expr.get(ID_C_class);
  if(!class_tag.empty())
    function_type.set(ID_C_class, class_tag);

  // Verify that the actual arguments are compatible with the deduced
  // parameter types.  Template argument deduction may succeed even when
  // the deduced types don't match (e.g., deducing T=int from the second
  // parameter of operator-(const complex<T>&, const T&) when the first
  // argument is an enum, not complex<int>).
  if(function_type.id() == ID_code && fargs.in_use)
  {
    const auto &params = to_code_type(function_type).parameters();
    auto arg_it = fargs.operands.begin();
    // skip 'this' parameter
    std::size_t start = (fargs.has_object && !params.empty()) ? 1 : 0;
    for(std::size_t i = start;
        i < params.size() && arg_it != fargs.operands.end();
        ++i, ++arg_it)
    {
      const typet &param_type = params[i].type();
      typet arg_type = arg_it->type();
      typet target = param_type;
      if(is_reference(target))
        target = to_reference_type(target).base_type();
      target.remove(ID_C_constant);
      target.remove(ID_C_volatile);
      arg_type.remove(ID_C_constant);
      arg_type.remove(ID_C_volatile);
      // If the parameter is a class/struct type and the argument is
      // not, the template is not a valid match.
      if(
        (target.id() == ID_struct_tag || target.id() == ID_struct) &&
        target != arg_type && arg_type.id() != ID_struct_tag &&
        arg_type.id() != ID_struct)
      {
        // Allow reference-to-struct to match struct_tag target
        if(
          arg_type.id() == ID_pointer &&
          (arg_type.get_bool(ID_C_reference) ||
           arg_type.get_bool(ID_C_rvalue_reference)))
        {
          // The base type of the reference should match the target
          // (this handles the case where _Compare&& deduces _Compare
          // from an lvalue reference argument)
        }
        else
        {
          return nil_exprt();
        }
      }
    }
  }

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
  if(expr.id() != ID_symbol)
    return; // templates are always symbols

  const symbolt &template_symbol =
    cpp_typecheck.lookup(to_symbol_expr(expr).get_identifier());

  if(!template_symbol.type.get_bool(ID_is_template))
    return;

  // Skip partial specializations — they are considered during
  // instantiation of the primary template, not during lookup.
  if(template_symbol.type.find(ID_specialization_of).is_not_nil())
  {
    expr.make_nil();
    return;
  }

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

    template_args_tc = cpp_typecheck.typecheck_template_args(
      source_location, template_symbol, template_args_non_tc);
    // go back to where we used to be
  }

  // For function templates with unassigned (partial) args, skip
  // instantiation. Store the explicit args for later deduction.
  if(template_args_tc.has_unassigned())
  {
    expr.add(ID_C_template_arguments) = template_args_tc;
    return;
  }

  // a template is always a declaration
  const cpp_declarationt &cpp_declaration =
    to_cpp_declaration(template_symbol.type);

  // is it a class template or function template?
  if(cpp_declaration.is_class_template())
  {
    const symbolt &new_symbol = cpp_typecheck.instantiate_template(
      source_location, template_symbol, template_args_tc, template_args_tc);

    expr = type_exprt(struct_tag_typet(new_symbol.name));
    expr.add_source_location() = source_location;
  }
  else
  {
    // function template, method template, or variable template.
    // Instantiation may fail due to SFINAE (e.g., enable_if in the
    // return type).  Suppress errors and treat failure as deduction
    // failure so that other overloads can be considered.
    null_message_handlert null_handler;
    message_handlert &old_handler = cpp_typecheck.get_message_handler();
    const symbolt *new_sym_ptr = nullptr;
    try
    {
      cpp_typecheck.set_message_handler(null_handler);
      const symbolt &new_symbol = cpp_typecheck.instantiate_template(
        source_location, template_symbol, template_args_tc, template_args_tc);
      new_sym_ptr = &new_symbol;
    }
    catch(...)
    {
      cpp_typecheck.set_message_handler(old_handler);
      expr.make_nil();
      return;
    }
    cpp_typecheck.set_message_handler(old_handler);
    const symbolt &new_symbol = *new_sym_ptr;

    // Variable template: the type is not a function type
    if(new_symbol.type.id() != ID_code)
    {
      if(new_symbol.is_macro && new_symbol.value.is_not_nil())
        expr = new_symbol.value;
      else
        expr = symbol_exprt(new_symbol.name, new_symbol.type);
      expr.add_source_location() = source_location;
    }
    else
    {
      // check if it is a method
      const code_typet &code_type = to_code_type(new_symbol.type);

      if(
        !code_type.parameters().empty() &&
        code_type.parameters().front().get_this())
      {
        // do we have an object?
        if(fargs.has_object)
        {
          const symbolt &type_symb = cpp_typecheck.lookup(
            fargs.operands.begin()->type().get(ID_identifier));

          CHECK_RETURN(type_symb.type.id() == ID_struct);

          const struct_typet &struct_type = to_struct_type(type_symb.type);

          DATA_INVARIANT(
            struct_type.has_component(new_symbol.name),
            "method should exist in struct");

          member_exprt member(
            *fargs.operands.begin(), new_symbol.name, code_type);
          member.add_source_location() = source_location;
          expr.swap(member);
          return;
        }
      }

      expr = cpp_symbol_expr(new_symbol);
      expr.add_source_location() = source_location;
    }
  }
}

bool cpp_typecheck_resolvet::disambiguate_functions(
  const exprt &expr,
  unsigned &args_distance,
  const cpp_typecheck_fargst &fargs)
{
  args_distance = 0;

  if(expr.type().id() != ID_code || !fargs.in_use)
    return true;

  const code_typet &type = to_code_type(expr.type());

  if(expr.id() == ID_member || type.return_type().id() == ID_constructor)
  {
    // if it's a member, but does not have an object yet,
    // we add one
    if(!fargs.has_object)
    {
      const code_typet::parameterst &parameters = type.parameters();

      if(!parameters.empty() && parameters.front().get_this())
      {
        const code_typet::parametert &parameter = parameters.front();

        if(type.return_type().id() == ID_constructor)
        {
          // it's a constructor
          const typet &object_type =
            to_pointer_type(parameter.type()).base_type();
          symbol_exprt object(irep_idt(), object_type);
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
          new_fargs.add_object(to_member_expr(expr).compound());

          return new_fargs.match(type, args_distance, cpp_typecheck);
        }
      }
      else
      {
        // Template function instance without this parameter yet;
        // match directly against the parameters.
        return fargs.match(type, args_distance, cpp_typecheck);
      }
    }
  }
  else if(fargs.has_object)
  {
    // If the function type already has a 'this' parameter (e.g., an
    // instantiated member function template), match directly — fargs
    // already includes the object and the type already includes 'this'.
    if(!type.parameters().empty() && type.parameters().front().get_this())
    {
      return fargs.match(type, args_distance, cpp_typecheck);
    }

    // For template function instances (pre-instantiation), the function
    // type doesn't include 'this' yet.  Remove the object and try to
    // match; if that fails, still accept the candidate with a high
    // distance so it can be instantiated and checked properly later.
    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.remove_object();

    if(new_fargs.match(type, args_distance, cpp_typecheck))
      return true;

    if(expr.id() == ID_template_function_instance)
    {
      args_distance = 10000;
      return true;
    }

    return false;
  }
  else if(
    expr.id() == ID_symbol && !fargs.operands.empty() &&
    !type.parameters().empty() && type.parameters().front().get_this())
  {
    // Instantiated template member function (symbol_exprt with this
    // parameter) called without an explicit object — add a synthetic
    // this for matching purposes.
    const typet &object_type =
      to_pointer_type(type.parameters().front().type()).base_type();
    symbol_exprt object(irep_idt(), object_type);
    object.set(ID_C_lvalue, true);

    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.add_object(object);
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
      DATA_INVARIANT(id.is_scope, "should be scope");
      new_set.insert(&id);
    }
    else if(id.is_typedef())
    {
      irep_idt identifier = id.identifier;

      if(id.is_member)
      {
        // Member typedefs are stored as struct components, not as
        // standalone symbols. Look up the typedef's type through the
        // class scope and follow it to the underlying struct type.
        // The identifier for a member typedef component is the
        // class identifier + "::" + base_name, but the symbol table
        // stores it under the class tag. Look up the parent class
        // and find the component.
        const cpp_idt &parent = id.get_parent();
        const auto *class_sym =
          cpp_typecheck.symbol_table.lookup(parent.identifier);
        if(class_sym != nullptr && class_sym->type.id() == ID_struct)
        {
          for(const auto &comp : to_struct_type(class_sym->type).components())
          {
            if(
              comp.get_base_name() == id.base_name && comp.get_bool(ID_is_type))
            {
              typet t = comp.type();
              if(t.id() == ID_struct_tag)
              {
                const irep_idt &tag_id = to_struct_tag_type(t).get_identifier();
                auto it = cpp_typecheck.cpp_scopes.id_map.find(tag_id);
                if(it != cpp_typecheck.cpp_scopes.id_map.end())
                {
                  cpp_idt &class_id = *it->second;
                  if(class_id.is_scope)
                    new_set.insert(&class_id);
                }
              }
              break;
            }
          }
        }
        continue;
      }

      while(true)
      {
        if(identifier.empty())
          break;
        const symbolt &symbol = cpp_typecheck.lookup(identifier);
        CHECK_RETURN(symbol.is_type);

        // todo? maybe do enum here, too?
        if(symbol.type.id() == ID_struct)
        {
          // this is a scope, too!
          cpp_idt &class_id = cpp_typecheck.cpp_scopes.get_id(identifier);

          DATA_INVARIANT(class_id.is_scope, "should be scope");
          new_set.insert(&class_id);
          break;
        }
        else if(symbol.type.id() == ID_struct_tag)
        {
          const irep_idt &tag_id =
            to_struct_tag_type(symbol.type).get_identifier();
          auto it = cpp_typecheck.cpp_scopes.id_map.find(tag_id);
          if(it != cpp_typecheck.cpp_scopes.id_map.end())
          {
            cpp_idt &class_id = *it->second;
            if(class_id.is_scope)
              new_set.insert(&class_id);
          }
          break;
        }
        else if(symbol.type.id() == ID_c_enum_tag)
        {
          const irep_idt &tag_id =
            to_c_enum_tag_type(symbol.type).get_identifier();
          auto it = cpp_typecheck.cpp_scopes.id_map.find(tag_id);
          if(it != cpp_typecheck.cpp_scopes.id_map.end())
          {
            cpp_idt &class_id = *it->second;
            if(class_id.is_scope)
              new_set.insert(&class_id);
          }
          break;
        }
        else
          break;
      }
    }
    else if(id.id_class == cpp_scopet::id_classt::TEMPLATE)
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
    else if(id.id_class == cpp_scopet::id_classt::TEMPLATE_PARAMETER)
    {
      // std::cout << "X4\n";
      // a template parameter may evaluate to be a scope: it could
      // be instantiated with a class/struct/union/enum
      exprt e = cpp_typecheck.template_map.lookup(id.identifier);

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

      if(e.id() != ID_type)
        continue; // expressions are definitively not a scope

      if(e.type().id() == ID_template_parameter_symbol_type)
      {
        auto type = to_template_parameter_symbol_type(e.type());

        while(true)
        {
          irep_idt identifier = type.get_identifier();
          if(identifier.empty())
            break;

          const symbolt &symbol = cpp_typecheck.lookup(identifier);
          CHECK_RETURN(symbol.is_type);

          if(symbol.type.id() == ID_template_parameter_symbol_type)
            type = to_template_parameter_symbol_type(symbol.type);
          else if(
            symbol.type.id() == ID_struct || symbol.type.id() == ID_union ||
            symbol.type.id() == ID_c_enum)
          {
            // this is a scope, too!
            cpp_idt &class_id = cpp_typecheck.cpp_scopes.get_id(identifier);

            DATA_INVARIANT(class_id.is_scope, "should be scope");
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

void cpp_typecheck_resolvet::filter_for_namespaces(cpp_scopest::id_sett &id_set)
{
  // we only want namespaces
  for(cpp_scopest::id_sett::iterator it = id_set.begin();
      it != id_set.end();) // no it++
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
  // Argument-dependent lookup (ADL / Koenig lookup):
  // Search in the namespaces associated with the argument types.
  for(const auto &arg : fargs.operands)
  {
    if(arg.type().id() != ID_struct_tag && arg.type().id() != ID_union_tag)
      continue;

    const struct_union_typet &final_type =
      arg.type().id() == ID_struct_tag
        ? static_cast<const struct_union_typet &>(
            cpp_typecheck.follow_tag(to_struct_tag_type(arg.type())))
        : static_cast<const struct_union_typet &>(
            cpp_typecheck.follow_tag(to_union_tag_type(arg.type())));

    // Search in the struct's own scope (for friend declarations)
    const irep_idt &struct_name = final_type.get(ID_name);
    if(struct_name.empty())
      continue;
    auto scope_it = cpp_typecheck.cpp_scopes.id_map.find(struct_name);
    if(scope_it == cpp_typecheck.cpp_scopes.id_map.end())
      continue;
    cpp_scopet &scope = static_cast<cpp_scopet &>(*scope_it->second);
    auto tmp_set = scope.lookup(base_name, cpp_scopet::SCOPE_ONLY);
    id_set.insert(tmp_set.begin(), tmp_set.end());

    // Search all enclosing namespaces (proper ADL, including
    // inline namespaces like std::__cxx11)
    for(cpp_scopet *ns = &scope; ns != nullptr && !ns->is_root_scope();
        ns = &ns->get_parent())
    {
      if(ns->is_namespace())
      {
        tmp_set = ns->lookup(base_name, cpp_scopet::SCOPE_ONLY);
        id_set.insert(tmp_set.begin(), tmp_set.end());
      }
    }
  }
}

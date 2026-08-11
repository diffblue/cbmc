/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#ifdef DEBUG
#  include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/base_exceptions.h> // IWYU pragma: keep
#include <util/c_types.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_sfinae_context.h"
#include "cpp_template_qualifiers.h"
#include "cpp_type2name.h"
#include "cpp_typecheck_resolve.h"
#include "expr2cpp.h"

#include <algorithm>

namespace
{
cpp_scopet *id_map_lookup(cpp_scopest &scopes, const irep_idt &key)
{
  auto it = scopes.id_map.find(key);
  return it != scopes.id_map.end() ? static_cast<cpp_scopet *>(it->second)
                                   : nullptr;
}
} // namespace

std::string
cpp_typecheckt::template_suffix(const cpp_template_args_tct &template_args)
{
  // quick hack
  std::string result = "<";
  bool first = true;

  const cpp_template_args_tct::argumentst &arguments =
    template_args.arguments();

  for(const auto &expr : arguments)
  {
    if(first)
      first = false;
    else
      result += ',';

    DATA_INVARIANT(
      expr.id() != ID_ambiguous, "template argument must not be ambiguous");

    if(expr.id() == ID_type)
    {
      const typet &type = expr.type();
      if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
      {
        // Include cv-qualifiers so that T and const T are distinct
        // instantiations (e.g., forward<const X> vs forward<X>).
        if(type.get_bool(ID_C_constant))
          result += "const ";
        if(type.get_bool(ID_C_volatile))
          result += "volatile ";
        result += id2string(to_tag_type(type).get_identifier());
      }
      else
        result += cpp_type2name(type);
    }
    else // expression
    {
      // [temp.arg.nontype]: a non-type template argument is a
      // converted constant expression; fold constexpr calls in it.
      constant_expression_contextt constant_expression_guard{*this};
      exprt e = expr;

      // N5008 [temp.arg.nontype]/2: a non-type template argument for a
      // reference or pointer parameter designates an object (it is the
      // address of an object with static storage duration), not a value --
      // e.g. reference_counting<T>'s `const T &empty = T::blank`, whose
      // argument is `&T::blank`.  Build the instance-name suffix from the
      // object's identity (its symbol name) rather than folding the referenced
      // symbol to its value below: equal objects yield equal suffixes (so the
      // same specialization is reused) and distinct objects yield distinct
      // suffixes, while folding would both lose that identity and turn the
      // argument into address-of-a-value, which is not a constant expression.
      if(
        e.id() == ID_address_of && e.operands().size() == 1 &&
        e.operands().front().id() == ID_symbol)
      {
        result += '&';
        result +=
          id2string(to_symbol_expr(e.operands().front()).get_identifier());
        continue;
      }

      // Recursively resolve constant symbols to their values, so that
      // expressions like "1000000000000000000l * ::value" can be evaluated.
      // Multiple passes may be needed for chains of symbol references.
      for(int pass = 0; pass < 10; ++pass)
      {
        bool changed = false;
        e.visit_pre(
          [this, &changed](exprt &node)
          {
            if(node.id() == ID_symbol)
            {
              // Don't replace function references with their bodies:
              // the function field of a `side_effect_expr_function_call`
              // is a `symbol_exprt` whose `type.id()` is `ID_code` and
              // whose value is the function body.  Substituting that
              // replaces the call's function operand with a code block
              // and then any unresolved cpp_names in the body get
              // re-typechecked in the caller's scope (where class-scope
              // members like a constexpr `value` are not visible),
              // producing spurious "symbol '...' is unknown" errors at
              // source locations pointing back into the function body.
              // `cpp_is_pod` returns true for `ID_code` via the
              // "everything else is POD" default which is fine for data
              // POD checks but wrong here.
              if(node.type().id() == ID_code)
                return;
              const symbolt &symbol = lookup(to_symbol_expr(node).identifier());
              if(symbol.value.is_not_nil() && cpp_is_pod(symbol.type))
              {
                node = symbol.value;
                changed = true;
              }
            }
          });
        if(!changed)
          break;
        simplify(e, *this);
        if(e.is_constant())
          break;
      }

      // If a template's default non-type argument failed to
      // resolve (e.g. a reference-template-parameter whose default
      // names a member that doesn't exist on the actual template
      // argument type — like libstdc++-wrapping code using
      //   template<typename T, const T &empty = T::blank>
      // with T = std::basic_string, which has no `blank`), `e` is
      // nil.  Rather than fail with `expected constant expression,
      // but got '<<expr:nil>>'`, emit a placeholder suffix so the
      // instantiation can proceed (with an undefined value).  This
      // matches the "soft failure" behaviour of other template
      // argument fallbacks in this file.
      if(e.is_nil())
      {
        result += "<nil_default>";
        continue;
      }

      make_constant(e);

      // this must be a constant, which includes true/false
      mp_integer i;

      if(e == true)
        i = 1;
      else if(e == false)
        i = 0;
      else if(!e.is_constant())
      {
        // N5008 [temp.arg.nontype]/1-2: a non-type template argument for a
        // parameter of reference, pointer, or (C++20) class type designates an
        // object/value rather than a scalar constant -- e.g.
        // reference_counting<T>'s `template<typename T, const T &empty =
        // T::blank>`, whose argument is the static object `T::blank`.  Such an
        // argument is not a scalar constant, so forcing the integer conversion
        // below would violate `to_constant_expr`'s precondition and abort.
        // Use a stable textual representation of the argument for the instance
        // name instead (equal arguments yield equal suffixes, so the same
        // specialization is reused).
        result += cpp_type2name(e.type());
        result += ':';
        result += expr2cpp(e, *this);
      }
      else
      {
        // follow c_enum_tag to c_enum for to_integer
        if(e.type().id() == ID_c_enum_tag)
          e.type() = follow_tag(to_c_enum_tag_type(e.type()));

        if(to_integer(to_constant_expr(e), i))
        {
          // C++20: floating-point non-type template parameters
          if(
            e.is_constant() &&
            (e.type().id() == ID_floatbv || e.type().id() == ID_fixedbv ||
             e.type().id() == ID_double || e.type().id() == ID_float))
          {
            result += id2string(to_constant_expr(e).get_value());
          }
          else
          {
            error().source_location = expr.find_source_location();
            error() << "template argument expression expected to be "
                    << "scalar constant, but got '" << to_string(e) << "'"
                    << eom;
            throw 0;
          }
        }
        else
        {
          result += integer2string(i);
        }
      }
    }
  }

  result += '>';

  return result;
}

void cpp_typecheckt::show_instantiation_stack(std::ostream &out)
{
  for(const auto &e : instantiation_stack)
  {
    const symbolt &symbol = lookup(e.identifier);
    out << "instantiating '" << symbol.pretty_name << "' with <";

    forall_expr(a_it, e.full_template_args.arguments())
    {
      if(a_it != e.full_template_args.arguments().begin())
        out << ", ";

      if(a_it->id() == ID_type)
        out << to_string(a_it->type());
      else
        out << to_string(*a_it);
    }

    out << "> at " << e.source_location << '\n';
  }
}

/// Set up a scope as subscope of the template scope
cpp_scopet &cpp_typecheckt::sub_scope_for_instantiation(
  cpp_scopet &template_scope,
  const std::string &suffix)
{
  cpp_scopet::id_sett id_set =
    template_scope.lookup(suffix, cpp_scopet::SCOPE_ONLY);

  CHECK_RETURN(id_set.size() <= 1);

  if(id_set.size() == 1)
  {
    cpp_idt &cpp_id = **id_set.begin();
    CHECK_RETURN(cpp_id.is_template_scope());

    return static_cast<cpp_scopet &>(cpp_id);
  }
  else
  {
    cpp_scopet &sub_scope = template_scope.new_scope(suffix);
    sub_scope.id_class = cpp_idt::id_classt::TEMPLATE_SCOPE;
    sub_scope.prefix = template_scope.get_parent().prefix;
    sub_scope.suffix = suffix;
    sub_scope.add_using_scope(template_scope.get_parent());

    const std::string subscope_name =
      id2string(template_scope.identifier) + suffix;
    cpp_scopes.id_map.insert(
      cpp_scopest::id_mapt::value_type(subscope_name, &sub_scope));

    return sub_scope;
  }
}

/// N5008 [temp.variadic]/5,7: expand pack-expansion mem-initializers of an
/// instantiated constructor into one initializer per pack element, with every
/// referenced pack -- TYPE packs (\p pack_args_map) and NON-TYPE packs
/// (\p pack_expr_map) alike -- substituted in lockstep.  libstdc++ pair's
/// piecewise target constructor `first(forward<_Args1>(get<_Indexes1>(
/// __tuple1))...)` mixes a reference-type pack with a non-type pack; the
/// previous single-name identifier rewrite (struct_tag one-element type packs
/// only) left the raw names and the ellipsis behind, the initializer failed
/// to convert, and the constructed pair was silently dropped.
static void expand_member_initializer_packs(
  irept &member_initializers,
  const template_mapt::pack_args_mapt &pack_args_map,
  const template_mapt::pack_expr_mapt &pack_expr_map)
{
  std::map<std::string, std::vector<typet>> type_packs;
  std::map<std::string, std::vector<exprt>> expr_packs;
  auto short_name = [](const irep_idt &full) -> std::string
  {
    const std::string f = id2string(full);
    auto pos = f.rfind("::");
    return pos != std::string::npos ? f.substr(pos + 2) : f;
  };
  for(const auto &pa : pack_args_map)
    type_packs[short_name(pa.first)] = pa.second;
  for(const auto &pe : pack_expr_map)
    expr_packs[short_name(pe.first)] = pe.second;
  if(type_packs.empty() && expr_packs.empty())
    return;

  std::function<bool(const irept &, std::size_t &)> pack_arity =
    [&](const irept &n, std::size_t &arity) -> bool
  {
    bool found = false;
    if(n.id() == ID_name)
    {
      const std::string id = id2string(n.get(ID_identifier));
      auto t_it = type_packs.find(id);
      auto e_it = expr_packs.find(id);
      if(t_it != type_packs.end())
      {
        arity = t_it->second.size();
        found = true;
      }
      else if(e_it != expr_packs.end())
      {
        arity = e_it->second.size();
        found = true;
      }
    }
    for(const auto &sn : n.get_sub())
      if(pack_arity(sn, arity))
        found = true;
    for(const auto &ns : n.get_named_sub())
      if(pack_arity(ns.second, arity))
        found = true;
    return found;
  };

  // substitute element k of every referenced pack: a cpp_name that is a
  // SINGLE name naming a type pack becomes the element type, one naming a
  // non-type pack the element value
  std::function<void(irept &, std::size_t)> subst_elem =
    [&](irept &n, std::size_t k)
  {
    if(n.id() == ID_cpp_name)
    {
      irep_idt only_name;
      bool single = true;
      for(const auto &sub : n.get_sub())
      {
        if(sub.id() == ID_name)
        {
          if(!only_name.empty())
            single = false;
          only_name = sub.get(ID_identifier);
        }
        else
          single = false;
      }
      if(single)
      {
        auto t_it = type_packs.find(id2string(only_name));
        if(t_it != type_packs.end() && k < t_it->second.size())
        {
          n = t_it->second[k];
          return;
        }
        auto e_it = expr_packs.find(id2string(only_name));
        if(e_it != expr_packs.end() && k < e_it->second.size())
        {
          n = e_it->second[k];
          return;
        }
      }
    }
    for(auto &sub : n.get_sub())
      subst_elem(sub, k);
    for(auto &ns : n.get_named_sub())
      subst_elem(ns.second, k);
  };

  irept::subt new_inits;
  for(auto &init : member_initializers.get_sub())
  {
    std::size_t arity = 0;
    if(init.get_bool(ID_ellipsis) && pack_arity(init, arity))
    {
      // whole-initializer expansion (a base/member pack)
      for(std::size_t k = 0; k < arity; ++k)
      {
        irept copy = init;
        copy.remove(ID_ellipsis);
        subst_elem(copy, k);
        new_inits.push_back(std::move(copy));
      }
      // arity 0: the initializer vanishes ([temp.variadic]/7)
    }
    else
    {
      // argument-level expansion: `member(pattern...)` -- each
      // ellipsis-carrying argument becomes one argument per element
      irept::subt new_args;
      bool changed = false;
      for(auto &a : init.get_sub())
      {
        std::size_t a_arity = 0;
        if(a.get_bool(ID_ellipsis) && pack_arity(a, a_arity))
        {
          for(std::size_t k = 0; k < a_arity; ++k)
          {
            irept copy = a;
            copy.remove(ID_ellipsis);
            subst_elem(copy, k);
            new_args.push_back(std::move(copy));
          }
          changed = true;
        }
        else
          new_args.push_back(a);
      }
      if(changed)
        init.get_sub().swap(new_args);
      new_inits.push_back(init);
    }
  }
  member_initializers.get_sub().swap(new_inits);
}

/// Walk \p node and apply expand_member_initializer_packs to every
/// member-initializer statement found (the form mem-initializers take once
/// they are part of a constructor's body).
void expand_member_initializer_packs_in_body(
  irept &node,
  const template_mapt::pack_args_mapt &pack_args_map,
  const template_mapt::pack_expr_mapt &pack_expr_map)
{
  if(node.id() == ID_code && node.get(ID_statement) == ID_member_initializer)
  {
    // wrap: the helper expects a list of initializers
    irept list;
    list.get_sub().push_back(node);
    expand_member_initializer_packs(list, pack_args_map, pack_expr_map);
    if(list.get_sub().size() == 1)
      node = list.get_sub().front();
    return;
  }
  for(auto &sub : node.get_sub())
    expand_member_initializer_packs_in_body(sub, pack_args_map, pack_expr_map);
  for(auto &ns : node.get_named_sub())
    expand_member_initializer_packs_in_body(
      ns.second, pack_args_map, pack_expr_map);
}

/// Create or find the symbol for a class template instantiation.
///
/// Per [temp.inst]/1, class template specializations are implicitly
/// instantiated when referenced.  This function creates the incomplete
/// type symbol (marked with template_class_instance) that will be
/// elaborated later by elaborate_class_template.
///
/// When the symbol already exists (e.g., from a forward declaration in
/// libc++-20's __fwd/ headers), ensures that template metadata
/// (ID_C_template, ID_C_template_arguments) is set so that template
/// argument deduction ([temp.deduct.type]/3.3) can match instantiation
/// arguments.
const symbolt &cpp_typecheckt::class_template_symbol(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_tct &specialization_template_args,
  const cpp_template_args_tct &full_template_args)
{
  // N5008 [temp.deduct.type]/8: a deduced template-template-parameter
  // is bound to the argument INSTANCE (see cpp_typecheck_resolve.cpp);
  // when such a binding flows here as the "template" to instantiate
  // with NEW arguments (`_Alloc<_Tp>` inside a partial-specialization
  // body -- libc++ __allocator_traits_rebind's
  // `_Alloc<_Tp>::template rebind<_Up>`), derive the TEMPLATE the
  // instance was created from.  Otherwise the instance symbol has no
  // template scope and instantiation fails ("template scope
  // 'tag-allocator<...>' not found"), dropping std::set's
  // __node_allocator typedef chain.
  if(
    !template_symbol.type.get_bool(ID_is_template) &&
    (template_symbol.type.id() == ID_struct ||
     template_symbol.type.id() == ID_union) &&
    template_symbol.type.find(ID_full_template_args).is_not_nil())
  {
    const auto tmpl_ids = cpp_scopes.get_root_scope().lookup(
      template_symbol.base_name,
      cpp_scopet::RECURSIVE,
      cpp_idt::id_classt::TEMPLATE);
    for(const auto *tid : tmpl_ids)
    {
      const symbolt *cand = symbol_table.lookup(tid->identifier);
      if(
        cand != nullptr && cand->type.get_bool(ID_is_template) &&
        to_cpp_declaration(cand->type).type().get(ID_specialization_of).empty())
      {
        return class_template_symbol(
          source_location,
          *cand,
          specialization_template_args,
          full_template_args);
      }
    }
  }

  if(full_template_args.has_unassigned())
  {
    // Template arguments contain unresolved parameters (e.g., from a
    // template constructor like optional(const optional<_Up>&) where
    // _Up is the constructor's own template parameter). Create an
    // incomplete type symbol so that callers get a proper type symbol
    // (with "tag-" prefix) rather than the template declaration symbol.
    std::string suffix = template_suffix(full_template_args);

    cpp_scopet *template_scope =
      id_map_lookup(cpp_scopes, template_symbol.name);
    if(template_scope == nullptr)
      return template_symbol;

    irep_idt identifier = id2string(template_scope->get_parent().prefix) +
                          "tag-" + id2string(template_symbol.base_name) +
                          id2string(suffix);

    auto s_it = symbol_table.symbols.find(identifier);
    if(s_it != symbol_table.symbols.end())
      return s_it->second;

    const cpp_declarationt &template_decl =
      to_cpp_declaration(template_symbol.type);
    const bool is_union = template_decl.type().id() == ID_union;
    type_symbolt new_symbol{
      identifier,
      is_union ? static_cast<typet>(union_typet()) : struct_typet(),
      template_symbol.mode};
    new_symbol.base_name = template_symbol.base_name;
    new_symbol.location = template_symbol.location;
    to_struct_union_type(new_symbol.type).make_incomplete();

    symbolt *s_ptr;
    symbol_table.move(new_symbol, s_ptr);
    return *s_ptr;
  }

  // do we have args?
  if(full_template_args.arguments().empty())
  {
    // Empty args are valid for:
    // 1. Variadic templates with zero arguments (e.g., tuple<>)
    // 2. Explicit specializations with zero parameters
    const template_typet &template_type =
      to_cpp_declaration(template_symbol.type).template_type();
    const auto &params = template_type.template_parameters();
    bool valid_empty = params.empty();
    if(!valid_empty)
    {
      valid_empty = true;
      for(const auto &p : params)
      {
        if(!p.get_bool(ID_ellipsis))
        {
          valid_empty = false;
          break;
        }
      }
    }
    if(!valid_empty)
    {
      error().source_location = source_location;
      error() << "'" << template_symbol.base_name
              << "' is a template; thus, expected template arguments" << eom;
      throw 0;
    }
  }

  // produce new symbol name
  std::string suffix = template_suffix(full_template_args);

  cpp_scopet *template_scope = id_map_lookup(cpp_scopes, template_symbol.name);

  if(template_scope == nullptr)
  {
    error().source_location = source_location;
    error() << "template scope '" << template_symbol.base_name << "' not found"
            << eom;
    throw 0;
  }

  irep_idt identifier = id2string(template_scope->get_parent().prefix) +
                        "tag-" + id2string(template_symbol.base_name) +
                        id2string(suffix);

  // already there?
  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find(identifier);
  if(s_it != symbol_table.symbols.end())
  {
    // The symbol may have been created by a forward declaration
    // (e.g., libc++-20's __fwd/ headers) without template metadata.
    // Set ID_C_template and ID_C_template_arguments so that template
    // argument deduction can match instantiation arguments later.
    if(symbolt *ws = symbol_table.get_writeable(identifier))
    {
      if(ws->type.find(ID_C_template).is_nil())
      {
        ws->type.set(
          ID_C_template,
          to_cpp_declaration(template_symbol.type).template_type());
        ws->type.set(ID_C_template_arguments, specialization_template_args);
      }
    }
    return s_it->second;
  }

  // Create as incomplete struct/union, but mark as
  // "template_class_instance", to be elaborated later.
  const cpp_declarationt &template_decl =
    to_cpp_declaration(template_symbol.type);
  const bool is_union = template_decl.type().id() == ID_union;
  type_symbolt new_symbol{
    identifier,
    is_union ? static_cast<typet>(union_typet()) : struct_typet(),
    template_symbol.mode};
  new_symbol.pretty_name = template_symbol.pretty_name;
  new_symbol.location = template_symbol.location;
  to_struct_union_type(new_symbol.type).make_incomplete();
  new_symbol.type.set(ID_tag, template_symbol.type.find(ID_tag));
  if(template_symbol.type.get_bool(ID_C_class))
    new_symbol.type.set(ID_C_class, true);
  new_symbol.type.set(ID_template_class_instance, true);
  new_symbol.type.add_source_location() = template_symbol.location;
  new_symbol.type.set(
    ID_specialization_template_args, specialization_template_args);
  new_symbol.type.set(ID_full_template_args, full_template_args);
  new_symbol.type.set(ID_identifier, template_symbol.name);
  new_symbol.base_name = template_symbol.base_name;

  symbolt *s_ptr;
  symbol_table.move(new_symbol, s_ptr);

  // put into template scope
  cpp_idt &id = cpp_scopes.put_into_scope(*s_ptr, *template_scope);

  id.id_class = cpp_idt::id_classt::CLASS;
  id.is_scope = true;
  id.prefix = template_scope->get_parent().prefix +
              id2string(s_ptr->base_name) + id2string(suffix) + "::";
  id.class_identifier = s_ptr->name;
  id.id_class = cpp_idt::id_classt::CLASS;

  return *s_ptr;
}

/// Elaborate (instantiate) a class template instance.
///
/// Implements [temp.inst]/1: "Unless a class template specialization has been
/// explicitly instantiated or explicitly specialized, the class template
/// specialization is implicitly instantiated when the specialization is
/// referenced in a context that requires a completely-defined object type."
///
/// Also implements [temp.spec.partial.match]: when elaborating, searches
/// for the best-matching partial specialization using the rules from
/// [temp.spec.partial.order] and [temp.constr.order] (constraint ordering).

// Evaluate a constexpr function call with constant arguments.
// Returns the result as a constant expression, or nil if evaluation fails.
exprt try_evaluate_constexpr(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns)
{
  if(expr.id() != ID_side_effect)
    return nil_exprt();
  if(expr.get(ID_statement) != ID_function_call)
    return nil_exprt();

  const auto &call = to_side_effect_expr_function_call(expr);
  const auto &function = call.function();
  const auto &arguments = call.arguments();

  // All arguments must be constants (or address_of for reference
  // parameters, possibly wrapping a temporary with a constant value).
  for(const auto &arg : arguments)
  {
    if(arg.is_constant())
      continue;
    if(arg.id() == ID_address_of)
    {
      const auto &obj = to_address_of_expr(arg).object();
      if(obj.is_constant())
        continue;
      if(
        obj.id() == ID_side_effect && obj.operands().size() == 1 &&
        obj.operands()[0].is_constant())
        continue;
    }
    return nil_exprt();
  }

  // Look up the function body
  if(function.id() != ID_symbol)
    return nil_exprt();
  const irep_idt &func_id = to_symbol_expr(function).get_identifier();
  const symbolt *func_sym = symbol_table.lookup(func_id);
  if(!func_sym || func_sym->value.is_nil())
    return nil_exprt();

  const auto &body = func_sym->value;
  if(body.id() != ID_code)
    return nil_exprt();
  // Guard against re-entrant evaluation
  static int eval_depth = 0;
  if(eval_depth > 10)
    return nil_exprt();
  ++eval_depth;
  struct depth_guardt
  {
    ~depth_guardt()
    {
      --eval_depth;
    }
  } dg;

  // Get parameter names
  const auto &func_type = to_code_type(func_sym->type);
  const auto &params = func_type.parameters();
  if(params.size() != arguments.size())
    return nil_exprt();

  // Build a variable map: parameter → constant value
  // For reference parameters, unwrap address_of and temporaries.
  std::map<irep_idt, exprt> vars;
  for(std::size_t i = 0; i < params.size(); ++i)
  {
    if(arguments[i].id() == ID_address_of)
    {
      const auto &obj = to_address_of_expr(arguments[i]).object();
      if(obj.is_constant())
        vars[params[i].get_identifier()] = obj;
      else if(
        obj.id() == ID_side_effect && obj.operands().size() == 1 &&
        obj.operands()[0].is_constant())
        vars[params[i].get_identifier()] = obj.operands()[0];
      else
        vars[params[i].get_identifier()] = arguments[i];
    }
    else
      vars[params[i].get_identifier()] = arguments[i];
  }

  // Mini-interpreter: execute the body with bounded iterations
  std::function<std::optional<exprt>(const codet &, int)> execute;
  std::function<exprt(const exprt &)> eval;

  eval = [&](const exprt &e) -> exprt
  {
    if(e.id() == ID_symbol)
    {
      auto it = vars.find(to_symbol_expr(e).get_identifier());
      if(it != vars.end())
        return it->second;
      return e;
    }
    // dereference(symbol) where symbol maps to a constant:
    // the parameter is a reference, unwrap the dereference.
    if(
      e.id() == ID_dereference && e.operands().size() == 1 &&
      e.operands()[0].id() == ID_symbol)
    {
      auto it = vars.find(to_symbol_expr(e.operands()[0]).get_identifier());
      if(it != vars.end() && it->second.is_constant())
        return it->second;
    }
    if(e.id() == ID_side_effect && e.get(ID_statement) == ID_function_call)
    {
      // Recursively evaluate nested function calls
      exprt evaluated = try_evaluate_constexpr(e, symbol_table, ns);
      if(evaluated.is_not_nil())
        return evaluated;
    }
    // Rebuild expression with evaluated operands
    exprt result = e;
    for(auto &op : result.operands())
      op = eval(op);
    // Try to simplify
    simplify(result, ns);
    return result;
  };

  execute = [&](const codet &code, int depth) -> std::optional<exprt>
  {
    if(depth > 100)
      return std::nullopt;

    if(code.get_statement() == ID_return)
    {
      if(code.operands().size() == 1)
        return eval(code.op0());
      return std::nullopt;
    }
    if(code.get_statement() == ID_block)
    {
      for(const auto &stmt : code.operands())
      {
        if(stmt.id() != ID_code)
          continue;
        auto r = execute(to_code(stmt), depth + 1);
        if(r.has_value())
          return r;
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_ifthenelse)
    {
      exprt cond = eval(code.op0());
      if(cond.is_true() && code.operands()[1].id() == ID_code)
        return execute(to_code(code.operands()[1]), depth + 1);
      if(
        cond.is_false() && code.operands().size() > 2 &&
        code.operands()[2].id() == ID_code)
        return execute(to_code(code.operands()[2]), depth + 1);
      if(cond.is_false())
        return std::nullopt;
      return std::nullopt; // can't evaluate condition
    }
    if(code.get_statement() == ID_while)
    {
      for(int iter = 0; iter < 64; ++iter)
      {
        exprt cond = eval(code.op0());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true())
          return std::nullopt; // can't evaluate condition
        if(code.operands()[1].id() != ID_code)
          return std::nullopt;
        auto r = execute(to_code(code.operands()[1]), depth + 1);
        if(r.has_value())
          return r;
      }
      return std::nullopt; // too many iterations
    }
    if(code.get_statement() == ID_dowhile)
    {
      // C++ [stmt.dowhile]: the body is executed BEFORE the condition is
      // evaluated.  Needed for e.g. libstdc++ chrono duration's constexpr
      // `_S_gcd`, whose do-while body computes the gcd used in the
      // `__divide` member alias's default template arguments; without it
      // the constant evaluation gave up and the __is_harmonic constraint
      // degraded to false.
      for(int iter = 0; iter < 64; ++iter)
      {
        if(code.operands()[1].id() != ID_code)
          return std::nullopt;
        auto r = execute(to_code(code.operands()[1]), depth + 1);
        if(r.has_value())
          return r;
        exprt cond = eval(code.op0());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true())
          return std::nullopt; // can't evaluate condition
      }
      return std::nullopt; // too many iterations
    }
    if(code.get_statement() == ID_assign)
    {
      const auto &lhs = code.op0();
      exprt rhs = eval(code.op1());
      if(lhs.id() == ID_symbol)
        vars[to_symbol_expr(lhs).get_identifier()] = rhs;
      return std::nullopt;
    }
    if(code.get_statement() == ID_decl)
    {
      // Variable declaration: bind the declared variable to its
      // initializer's VALUE when one is present ([dcl.init]); only
      // default-initialize to zero when there is none.  Dropping the
      // initializer made e.g. the loop-local remainder in chrono
      // duration's constexpr _S_gcd start at zero, corrupting the gcd.
      if(code.operands().size() > 0 && code.op0().id() == ID_symbol)
      {
        const auto &sym = to_symbol_expr(code.op0());
        if(code.operands().size() >= 2)
        {
          exprt init = eval(code.op1());
          if(!init.is_constant())
            return std::nullopt; // can't track this variable's value
          vars[sym.get_identifier()] = init;
        }
        else
          vars[sym.get_identifier()] = from_integer(0, sym.type());
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_expression)
    {
      // An expression statement may BE an assignment
      // (`side_effect statement=assign`), e.g. the `__m = __n; __n = __rem;`
      // steps of chrono duration's constexpr _S_gcd do-while body.  Apply
      // it to the tracked variables; skipping it froze the loop variables,
      // so the termination condition never changed and evaluation gave up.
      if(!code.operands().empty())
      {
        const exprt &e = code.op0();
        if(
          e.id() == ID_side_effect && e.get(ID_statement) == ID_assign &&
          e.operands().size() == 2 && e.operands()[0].id() == ID_symbol)
        {
          exprt rhs = eval(e.operands()[1]);
          if(!rhs.is_constant())
            return std::nullopt; // lost track of a variable's value
          vars[to_symbol_expr(e.operands()[0]).get_identifier()] = rhs;
        }
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_skip)
      return std::nullopt;

    return std::nullopt; // unknown statement
  };

  auto result = execute(to_code(body), 0);
  if(result.has_value())
  {
    if(result->is_constant())
      return *result;
    // Reference-returning functions (like std::max) return
    // address_of(constant).  Unwrap to the constant.
    if(
      result->id() == ID_address_of &&
      to_address_of_expr(*result).object().is_constant())
    {
      return to_address_of_expr(*result).object();
    }
  }

  return nil_exprt();
}

struct_union_typet::componentt *cpp_typecheckt::ensure_member_complete(
  struct_union_typet &struct_type,
  const irep_idt &base_name)
{
  // Phase 3 narrow producer + Phase 4 on-demand resolution per
  // N5008 [temp.inst]/3.1.  When a component carries the
  // `ID_C_lazy_member_type` marker, its declared type is an
  // unresolved cpp_name placeholder kept by the producer in
  // `typecheck_compound_body`.  This entry point is the consumer
  // side: it locates the named component, and if it is lazy, makes
  // a single best-effort attempt to resolve the placeholder under
  // the original class scope and SFINAE protection
  // ([temp.deduct]/8).  On success the component's type is
  // replaced with the resolved type and the marker cleared; on
  // failure the placeholder is left in place so subsequent calls
  // can retry (idempotent), and the marker remains visible to
  // callers that want to skip rather than read an incomplete type.
  for(auto &c : struct_type.components())
  {
    if(c.get_base_name() != base_name)
      continue;
    if(c.get_bool(ID_C_lazy_member_type))
      try_resolve_lazy_member(c);
    return &c;
  }
  return nullptr;
}

const struct_union_typet::componentt *cpp_typecheckt::ensure_member_complete(
  const struct_union_typet &struct_type,
  const irep_idt &base_name)
{
  // Read-only entry point.  Cannot mutate, so cannot run the
  // resolution attempt; returns the component as-is.  Callers that
  // need a resolved type should check `get_bool(ID_C_lazy_member_type)`
  // and either skip or take the mutable overload.
  for(const auto &c : struct_type.components())
  {
    if(c.get_base_name() != base_name)
      continue;
    return &c;
  }
  return nullptr;
}

void cpp_typecheckt::complete_all_components(struct_union_typet &struct_type)
{
  // Phase 4: bulk on-demand resolution.  Iterates every component
  // once and tries to resolve any lazy ones.  Components that
  // remain unresolved keep their marker.
  for(auto &c : struct_type.components())
  {
    if(c.get_bool(ID_C_lazy_member_type))
      try_resolve_lazy_member(c);
  }
}

bool cpp_typecheckt::try_resolve_lazy_member(
  struct_union_typet::componentt &component)
{
  // Per N5008 [temp.inst]/3.1 with [temp.deduct]/8 protection: try
  // to resolve a lazy component's placeholder type one more time.
  // The producer in `typecheck_compound_body` saved the class scope
  // identifier under `ID_lazy_type_source` so the retry can be
  // performed in the right context — typedef and member name
  // lookups within the unresolved cpp_name need the class scope to
  // resolve sibling members.
  if(!component.get_bool(ID_C_lazy_member_type))
    return true;

  const irep_idt class_scope_id = component.get(ID_lazy_type_source);
  if(class_scope_id.empty())
    return false;

  auto scope_it = cpp_scopes.id_map.find(class_scope_id);
  if(scope_it == cpp_scopes.id_map.end())
    return false;

  cpp_save_scopet save{cpp_scopes};
  cpp_scopes.go_to(*scope_it->second);

  typet candidate = component.type();
  candidate.remove(ID_C_lazy_member_type);
  candidate.remove(ID_lazy_type_source);

  bool ok = true;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    typecheck_type(candidate);
  }
  catch(...)
  {
    ok = false;
  }

  if(!ok)
    return false;

  // Resolution succeeded: replace the component's type and clear
  // the lazy markers.  We deliberately do not touch any class-scope
  // typedef symbol that the producer may have created — that
  // symbol's type still needs the same resolution attempt, but
  // running it from a different lookup path could mean the symbol
  // and the component disagree if one path succeeds and the other
  // fails.  A separate Phase 4b pass will reconcile typedef
  // symbols at first use; for now they keep the placeholder.
  component.type() = std::move(candidate);
  return true;
}

bool cpp_typecheckt::try_resolve_lazy_typedef_symbol(symbolt &sym)
{
  // Sibling of `try_resolve_lazy_member` for the class-scope
  // typedef *symbols* registered by the producer.  The original
  // declaration's class scope is stamped under `ID_lazy_type_source`
  // on the alias type itself.  Stripping the markers from a working
  // copy and running `typecheck_type` under `sfinae_contextt` lets
  // the retry happen at the use site without leaking diagnostics or
  // mutating the symbol on failure.  On success the symbol's type
  // becomes the resolved type and subsequent lookups (resolver,
  // callers of `typecheck_type`) see a normal complete type.
  //
  // Guard against re-entering the class while it is itself being
  // typechecked: if the current scope (or any nested scope) is the
  // lazy class itself, we are still inside that class's body or a
  // nested scope of it.  Defer the retry — the class is
  // mid-construction and triggering elaboration here would loop
  // back into the in-progress class body.  The retry is only safe
  // at use sites *outside* the declaring class's body, where
  // method-body typechecking has started and the class scope is
  // fully populated.
  if(!sym.type.get_bool(ID_C_lazy_member_type))
    return true;

  const irep_idt class_scope_id = sym.type.get(ID_lazy_type_source);
  if(class_scope_id.empty())
    return false;

  auto cls_scope_it = cpp_scopes.id_map.find(class_scope_id);
  if(cls_scope_it == cpp_scopes.id_map.end())
    return false;

  // Re-entry guard: defer the retry only when we are *currently*
  // inside the lazy class scope itself — that is the case where
  // `typecheck_compound_body` is still constructing the class and
  // a recursive `typecheck_type` would loop.  Method-body scopes
  // nested inside the class (e.g. `C::method::`) are safe: the
  // class is fully populated by then and member-typedef references
  // can legitimately drive resolution.  An exact-prefix check
  // distinguishes the two: class body construction reaches the
  // typedef-resolution path with `current_scope().prefix` equal to
  // the class's prefix; method-body typechecking has a longer
  // prefix.
  const std::string &cur_prefix = cpp_scopes.current_scope().prefix;
  const std::string &cls_prefix = cls_scope_it->second->prefix;
  if(!cls_prefix.empty() && cur_prefix == cls_prefix)
    return false;

  cpp_save_scopet save{cpp_scopes};
  cpp_scopes.go_to(*cls_scope_it->second);

  typet candidate = sym.type;
  candidate.remove(ID_C_lazy_member_type);
  candidate.remove(ID_lazy_type_source);

  bool ok = true;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    typecheck_type(candidate);
  }
  catch(...)
  {
    ok = false;
  }

  if(!ok)
    return false;

  sym.type = std::move(candidate);
  return true;
}

bool cpp_typecheckt::try_resolve_lazy_type(typet &type)
{
  // Type-only on-demand resolution.  Same mechanic as
  // `try_resolve_lazy_typedef_symbol` and `try_resolve_lazy_member`
  // but operates directly on a typet — useful at sites that have a
  // copy of the type but not a back-pointer to the originating
  // symbol or component.
  if(!type.get_bool(ID_C_lazy_member_type))
    return true;

  const irep_idt class_scope_id = type.get(ID_lazy_type_source);
  if(class_scope_id.empty())
    return false;

  auto cls_scope_it = cpp_scopes.id_map.find(class_scope_id);
  if(cls_scope_it == cpp_scopes.id_map.end())
    return false;

  // Re-entry guard: defer if the current scope IS the lazy class
  // (mid-construction).  Method-body or other nested scopes are
  // safe.
  const std::string &cur_prefix = cpp_scopes.current_scope().prefix;
  const std::string &cls_prefix = cls_scope_it->second->prefix;
  if(!cls_prefix.empty() && cur_prefix == cls_prefix)
    return false;

  cpp_save_scopet save{cpp_scopes};
  cpp_scopes.go_to(*cls_scope_it->second);

  typet candidate = type;
  candidate.remove(ID_C_lazy_member_type);
  candidate.remove(ID_lazy_type_source);

  bool ok = true;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    typecheck_type(candidate);
  }
  catch(...)
  {
    ok = false;
  }

  if(!ok)
    return false;

  type = std::move(candidate);
  return true;
}

/// True iff \p type carries the #dropped_incomplete_base marker AND the
/// recorded base type has meanwhile been COMPLETED, i.e. re-elaboration
/// at this new point of instantiation ([temp.point]) can now succeed.
bool cpp_typecheckt::dropped_base_now_complete(const typet &type) const
{
  const irep_idt base_id = type.get("#dropped_incomplete_base");
  if(base_id.empty())
    return false;
  const symbolt *base_sym = symbol_table.lookup(base_id);
  return base_sym != nullptr &&
         (base_sym->type.id() == ID_struct ||
          base_sym->type.id() == ID_union) &&
         !to_struct_union_type(base_sym->type).is_incomplete();
}

void cpp_typecheckt::elaborate_class_template(const typet &type)
{
  if(type.id() != ID_struct_tag && type.id() != ID_union_tag)
    return;

  // The tag-typed argument may carry an empty identifier when the
  // caller derived it from a partially-elaborated template instance
  // whose name resolution in turn produced a malformed struct_tag.
  // The downstream `lookup(to_tag_type(type))` enforces a precondition
  // that the identifier is in the symbol table, which an empty
  // identifier always violates.  A SFINAE-style early return mirrors
  // the existing "type isn't a tag" early return above and keeps
  // recovery code paths in callers (e.g. resolve / typecheck_type)
  // from tripping a hard invariant when they pass through here on
  // their error-recovery branch.
  if(to_tag_type(type).get_identifier().empty())
    return;

  if(suppress_elaborate && !force_elaborate)
  {
    if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
    {
      const symbolt &sym = lookup(to_tag_type(type));
      if(
        (sym.type.id() == ID_struct || sym.type.id() == ID_union) &&
        sym.type.get_bool(ID_template_class_instance) &&
        (to_struct_union_type(sym.type).components().empty() ||
         to_struct_union_type(sym.type).is_incomplete() ||
         dropped_base_now_complete(sym.type)))
      {
        // Empty or incomplete template instance — allow elaboration
      }
      else
        return;
    }
    else
      return;
  }

  const symbolt &symbol = lookup(to_tag_type(type));

  // Make a copy, as instantiate will destroy the symbol type!
  const typet t_type = symbol.type;

  // When force-elaborating empty template instances, catch errors
  // to avoid breaking callers. Errors in system header templates
  // (e.g., compressed_pair reference initialization) are non-fatal.

  if(
    (t_type.id() == ID_struct || t_type.id() == ID_union) &&
    t_type.get_bool(ID_template_class_instance))
  {
    // If the instance already has components and is fully elaborated
    // (not incomplete), skip re-instantiation.  Re-elaborating can
    // fail when template arguments reference local scopes that are
    // no longer accessible.  Partially elaborated classes (incomplete
    // with some components) must still be re-elaborated.
    if(
      !to_struct_union_type(symbol.type).components().empty() &&
      !to_struct_union_type(symbol.type).is_incomplete() &&
      !dropped_base_now_complete(symbol.type))
    {
      return;
    }

    const irep_idt initial_template_name = t_type.get(ID_identifier);
    if(initial_template_name.empty())
    {
      // Defensive: if the template instance's underlying complete
      // type lacks `ID_identifier` (e.g. because it was produced by
      // an incomplete-to-complete swap that didn't set it), there is
      // no primary template to look up.  Without this guard
      // `lookup(initial_template_name)` would trip a
      // namespace-base lookup invariant.
      return;
    }
    const symbolt &initial_template = lookup(initial_template_name);
    // If the instance was created with a concept-constrained partial
    // specialization but is still empty, follow ID_specialization_of
    // to get the actual primary template. This re-does the
    // specialization search with concept evaluation, which may select
    // a more constrained specialization. Only do this for partial
    // specializations with concept constraints — full specializations
    // are always correct.
    bool has_concept_constraint = false;
    if(
      !initial_template.type.get(ID_specialization_of).empty() &&
      to_struct_union_type(symbol.type).components().empty())
    {
      const auto &tmpl_type =
        to_cpp_declaration(initial_template.type).template_type();
      for(const auto &p : tmpl_type.template_parameters())
        if(!p.get("#C_concept_constraint").empty())
          has_concept_constraint = true;
      // A requires-clause on the partial specialization is an associated
      // constraint ([temp.constr.decl]/1) just like a constrained
      // template parameter.  When several partial specializations share
      // the same argument pattern and differ only by their
      // requires-clauses (e.g. libstdc++'s three __iterator_traits
      // specializations), the most-constrained *satisfied* one must be
      // selected ([temp.class.spec.match]/2 with [temp.constr.order]).
      // Re-running the specialization search from the primary template
      // (below) performs that constraint-aware selection, so trigger it
      // for requires-clause-constrained specializations too -- otherwise
      // the arbitrary specialization matched first is kept.
      const irept &spec_req = tmpl_type.find(ID_C_requires_clause);
      if(spec_req.is_not_nil() && spec_req.id() != ID_nil)
        has_concept_constraint = true;
    }
    const symbolt &primary_template =
      has_concept_constraint
        ? lookup(initial_template.type.get(ID_specialization_of))
        : initial_template;

    // If this class template is already being instantiated with the
    // same arguments (on the instantiation stack), skip elaboration
    // to break infinite recursion. Also limit recursion depth for
    // the same primary template to prevent non-terminating chains.
    cpp_template_args_tct full_args =
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_full_template_args));
    // Simplify non-type template arguments so that expressions like
    // is_destructible<T>::value are constant-folded before
    // specialization matching.
    for(auto &arg : full_args.arguments())
    {
      if(arg.id() != ID_type && arg.id() != ID_ambiguous)
      {
        try
        {
          typecheck_expr(arg);
          simplify(arg, *this);
          // Try constexpr evaluation for remaining function calls
          {
            std::function<void(exprt &)> eval_calls;
            eval_calls = [&](exprt &e)
            {
              for(auto &op : e.operands())
                eval_calls(op);
              if(
                e.id() == ID_side_effect &&
                e.get(ID_statement) == ID_function_call)
              {
                exprt r = try_evaluate_constexpr(e, symbol_table, *this);
                if(r.is_not_nil())
                  e = r;
              }
              simplify(e, *this);
            };
            eval_calls(arg);
          }
          // Resolve symbol references to their constant values
          if(arg.id() == ID_symbol)
          {
            const auto *sym =
              symbol_table.lookup(to_symbol_expr(arg).get_identifier());
            if(
              sym && sym->is_macro && sym->value.is_not_nil() &&
              sym->value.is_constant())
              arg = sym->value;
          }
        }
        catch(...)
        {
        }
      }
    }
    unsigned same_template_depth = 0;
    bool has_converging_int_args = false;
    for(const auto &entry : instantiation_stack)
    {
      if(entry.identifier == primary_template.name)
      {
        if(entry.full_template_args == full_args)
        {
          // Allow re-elaboration if the instance is empty
          // (primary template was used, specialization matching
          // hasn't happened yet).
          if(to_struct_union_type(symbol.type).components().empty())
            break; // proceed with specialization matching
          return;
        }
        ++same_template_depth;
      }
    }

    // For templates with non-type integer arguments that are strictly
    // smaller than all parent instances of the same template, allow
    // deeper recursion (convergent recursion like Fibonacci).
    // For type-only arguments, keep the conservative limit.
    if(same_template_depth >= 2)
    {
      // Check if current args have a non-type integer constant that
      // is strictly less than the corresponding arg in every parent.
      for(const auto &arg : full_args.arguments())
      {
        if(arg.id() == ID_type || !arg.is_constant())
          continue;
        mp_integer current_val;
        if(to_integer(to_constant_expr(arg), current_val))
          continue;
        bool all_parents_larger = true;
        for(const auto &entry : instantiation_stack)
        {
          if(entry.identifier != primary_template.name)
            continue;
          bool found_larger = false;
          for(const auto &parg : entry.full_template_args.arguments())
          {
            if(parg.id() == ID_type || !parg.is_constant())
              continue;
            mp_integer parent_val;
            if(to_integer(to_constant_expr(parg), parent_val))
              continue;
            if(parent_val > current_val)
            {
              found_larger = true;
              break;
            }
          }
          if(!found_larger)
          {
            all_parents_larger = false;
            break;
          }
        }
        if(all_parents_larger)
        {
          has_converging_int_args = true;
          break;
        }
      }
      if(!has_converging_int_args)
        return;
    }

    const cpp_template_args_tct &specialization_args =
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_specialization_template_args));

    // Resolve symbol references in full_args, mirroring the logic
    // in template_suffix.
    cpp_template_args_tct full_args_tc = full_args;
    for(auto &arg : full_args_tc.arguments())
    {
      if(arg.id() == ID_type)
        continue;
      for(int pass = 0; pass < 10; ++pass)
      {
        bool changed = false;
        arg.visit_pre(
          [this, &changed](exprt &node)
          {
            if(node.id() == ID_symbol)
            {
              const symbolt &sym =
                lookup(to_symbol_expr(node).get_identifier());
              if(sym.value.is_not_nil() && cpp_is_pod(sym.type))
              {
                node = sym.value;
                changed = true;
              }
            }
          });
        if(!changed)
          break;
        simplify(arg, *this);
        if(arg.is_constant())
          break;
      }
    }

    // [temp.inst]/2: a class template specialization used as a template
    // argument is implicitly instantiated when its completeness affects
    // the semantics of the program.  Selecting a partial specialization
    // here matches the partial-specialization argument pattern against
    // these actual arguments ([temp.spec.partial.match]/2), which for a
    // nested class-template-id argument (e.g. the `holder<int>` in
    // `base<holder<int>>`, the libstdc++ `allocator_traits<allocator<T>>`
    // shape) requires that argument to be elaborated.  A type-naming
    // declaration of `base<holder<int>>` elaborates `holder<int>` as a
    // side effect of resolving the full type, but a qualified-name use
    // such as `base<holder<int>>::cp` reaches here with the argument
    // still incomplete.  Elaborate any incomplete class-template-instance
    // arguments up front so the specialization match (and the resulting
    // instantiation) is the same regardless of which context first
    // required the specialization ([temp.spec.general]/7: at most one
    // point of instantiation per translation unit).
    for(auto &arg : full_args_tc.arguments())
    {
      if(arg.id() != ID_type)
        continue;
      const typet &arg_type = arg.type();
      if(arg_type.id() != ID_struct_tag && arg_type.id() != ID_union_tag)
        continue;
      if(to_tag_type(arg_type).get_identifier().empty())
        continue;
      const symbolt &arg_sym = lookup(to_tag_type(arg_type));
      if(
        (arg_sym.type.id() == ID_struct || arg_sym.type.id() == ID_union) &&
        arg_sym.type.get_bool(ID_template_class_instance) &&
        to_struct_union_type(arg_sym.type).is_incomplete())
      {
        // SFINAE-style guard: if the argument cannot be elaborated this
        // is not necessarily fatal to the enclosing instantiation (the
        // match may still fall back to another candidate), mirroring the
        // recovery convention used elsewhere in this routine.
        try
        {
          elaborate_class_template(arg_type);
        }
        catch(...)
        {
        }
      }
    }

    // Search for a better-matching partial specialization only if
    // the symbol was created with the primary template (not already
    // matched to a partial specialization).
    const symbolt *best_match = &primary_template;
    cpp_template_args_tct best_spec_args = specialization_args;

    if(primary_template.type.get(ID_specialization_of).empty())
    {
      cpp_scopet *template_scope =
        id_map_lookup(cpp_scopes, primary_template.name);

      if(template_scope != nullptr)
      {
        cpp_scopet &scope = template_scope->get_parent();
        cpp_scopet::id_sett id_set =
          scope.lookup(primary_template.base_name, cpp_scopet::SCOPE_ONLY);

        // [temp.deduct]/8 + [temp.class.spec.match]: specialization
        // matching iterates candidate partial specializations; per-
        // candidate substitution failure is SFINAE, not a compile
        // error.
        sfinae_contextt spec_sfinae_guard{*this};

        // Scope the two-phase-lookup filter (see resolve()) to the
        // pattern matching below.
        struct two_phase_guardt
        {
          unsigned &d;
          explicit two_phase_guardt(unsigned &_d) : d(_d)
          {
            ++d;
          }
          ~two_phase_guardt()
          {
            --d;
          }
        } two_phase_guard{two_phase_pattern_depth};

        for(const auto *id_ptr : id_set)
        {
          const symbolt &s = lookup(id_ptr->identifier);
          if(s.type.get(ID_specialization_of).empty())
            continue;

          const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);
          const cpp_template_args_non_tct &partial_specialization_args =
            cpp_declaration.partial_specialization_args();

          if(
            partial_specialization_args.arguments().size() !=
            full_args_tc.arguments().size())
          {
            // Allow partial specialization to have more args than full
            // args when the extra args are variadic pack expansions
            // (which can match zero elements).
            bool size_ok = false;
            if(
              partial_specialization_args.arguments().size() >
              full_args_tc.arguments().size())
            {
              size_ok = true;
              for(std::size_t i = full_args_tc.arguments().size();
                  i < partial_specialization_args.arguments().size();
                  i++)
              {
                const auto &arg = partial_specialization_args.arguments()[i];
                if(
                  !arg.get_bool(ID_ellipsis) &&
                  !arg.type().get_bool(ID_ellipsis))
                {
                  size_ok = false;
                  break;
                }
              }
            }
            // N5008 [temp.spec.partial.match]/2: a TRAILING pack
            // pattern also matches a LONGER argument list (npat <
            // nfull), the pack absorbing the remainder --
            // `__tuple_impl<__tuple_indices<_Indx...>, _Tp...>` (2
            // pattern entries) vs `<__tuple_indices<0,1>, int, int>`
            // (3 arguments).  Only MULTI-pack heads take this path:
            // a single trailing pack is already handled correctly by
            // template_mapt::build from the flat list, and
            // double-binding regressed the recursive single-pack
            // shapes (cpp11_variadic_ctor_pack_multi).
            else if(
              !partial_specialization_args.arguments().empty() &&
              (partial_specialization_args.arguments().back().get_bool(
                 ID_ellipsis) ||
               partial_specialization_args.arguments().back().type().get_bool(
                 ID_ellipsis)))
            {
              std::size_t n_packs = 0;
              for(const auto &tp :
                  cpp_declaration.template_type().template_parameters())
                if(tp.get_bool(ID_ellipsis))
                  ++n_packs;
              size_ok = n_packs >= 2;
            }
            if(!size_ok)
              continue;
          }

          cpp_saved_template_mapt saved_map(template_map);
          cpp_save_scopet save_scope(cpp_scopes);

          template_map.build_unassigned(cpp_declaration.template_type());

          cpp_scopet *spec_scope = id_map_lookup(cpp_scopes, s.name);
          if(spec_scope != nullptr)
            cpp_scopes.go_to(*spec_scope);

          cpp_typecheck_resolvet resolver(*this);
          // [temp.deduct.type]/8: partial-specialization matching
          // rejects cv-mismatched patterns (see the flag's doc in
          // cpp_typecheck_resolve.h).
          resolver.strict_cv_deduction = true;

          {
            const std::size_t sel_npat =
              partial_specialization_args.arguments().size();
            const bool sel_trailing_pack =
              sel_npat > 0 &&
              (partial_specialization_args.arguments().back().get_bool(
                 ID_ellipsis) ||
               partial_specialization_args.arguments().back().type().get_bool(
                 ID_ellipsis));
            std::size_t sel_n_packs = 0;
            for(const auto &tp :
                cpp_declaration.template_type().template_parameters())
              if(tp.get_bool(ID_ellipsis))
                ++sel_n_packs;
            // N5008 [temp.spec.partial.match]/2 multi-pack case (see the
            // size gate above): positional prefix, then the trailing
            // pack absorbs the remainder as ONE pack -- per-argument
            // guessing against the pack pattern would overwrite the
            // binding with each element.
            const bool multi_pack_absorb =
              sel_trailing_pack && sel_n_packs >= 2 &&
              sel_npat <= full_args_tc.arguments().size();
            const std::size_t n_positional =
              multi_pack_absorb
                ? sel_npat - 1
                : std::min(sel_npat, full_args_tc.arguments().size());
            for(std::size_t i = 0; i < n_positional; i++)
            {
              if(full_args_tc.arguments()[i].id() == ID_type)
                resolver.guess_template_args(
                  partial_specialization_args.arguments()[i].type(),
                  full_args_tc.arguments()[i].type());
              else
                resolver.guess_template_args(
                  partial_specialization_args.arguments()[i],
                  full_args_tc.arguments()[i]);
            }
            if(!multi_pack_absorb && sel_npat > n_positional)
            {
              // original behaviour: remaining pattern entries (equal
              // or npat > nfull cases) guessed per argument position
              for(std::size_t i = n_positional;
                  i < full_args_tc.arguments().size() && i < sel_npat;
                  i++)
              {
                if(full_args_tc.arguments()[i].id() == ID_type)
                  resolver.guess_template_args(
                    partial_specialization_args.arguments()[i].type(),
                    full_args_tc.arguments()[i].type());
                else
                  resolver.guess_template_args(
                    partial_specialization_args.arguments()[i],
                    full_args_tc.arguments()[i]);
              }
            }
            if(multi_pack_absorb)
            {
              const auto &last = partial_specialization_args.arguments().back();
              const irept &last_t =
                last.id() == ID_ambiguous || last.id() == ID_type
                  ? static_cast<const irept &>(last.type())
                  : static_cast<const irept &>(last);
              irep_idt pack_id;
              if(
                last_t.id() == ID_cpp_name && !last_t.get_sub().empty() &&
                last_t.get_sub().front().id() == ID_name)
              {
                const irep_idt pn = last_t.get_sub().front().get(ID_identifier);
                const auto ids = cpp_scopes.current_scope().lookup(
                  pn,
                  cpp_scopet::RECURSIVE,
                  cpp_idt::id_classt::TEMPLATE_PARAMETER);
                for(const auto *idp : ids)
                  pack_id = idp->identifier;
              }
              if(!pack_id.empty())
              {
                std::vector<typet> pack_elems;
                std::vector<exprt> pack_exprs;
                for(std::size_t j = n_positional;
                    j < full_args_tc.arguments().size();
                    j++)
                {
                  const auto &a = full_args_tc.arguments()[j];
                  if(a.id() == ID_type)
                  {
                    if(a.type().id() != ID_empty)
                      pack_elems.push_back(a.type());
                  }
                  else if(a.id() != ID_unassigned)
                    pack_exprs.push_back(a);
                }
                template_map.pack_size_map[pack_id] =
                  pack_elems.size() + pack_exprs.size();
                // Scalar convenience entries only for SINGLE-element
                // packs: a >=2-element scalar CONCRETIZES the pack
                // reference in patterns (base-specifier / parameter
                // replication is keyed by NAME), collapsing e.g.
                // `__tuple_leaf<_Indx, _Tp>...` to the first element's
                // type for every leaf ([temp.variadic]/5; the
                // heterogeneous tuple<int,double,char> shape).
                if(!pack_exprs.empty())
                {
                  template_map.pack_expr_map[pack_id] = pack_exprs;
                  if(pack_exprs.size() == 1)
                    template_map.expr_map[pack_id] = pack_exprs.front();
                }
                else
                {
                  template_map.pack_args_map[pack_id] = pack_elems;
                  if(pack_elems.size() == 1)
                    template_map.type_map[pack_id] = pack_elems.front();
                }
              }
            }
          }

          cpp_template_args_tct guessed_args =
            template_map.build_template_args(cpp_declaration.template_type());

          // Variadic pack parameters that matched zero elements
          // remain unassigned. Set them to empty type arguments.
          if(guessed_args.has_unassigned())
          {
            const auto &tparams =
              cpp_declaration.template_type().template_parameters();
            for(std::size_t i = 0; i < tparams.size(); i++)
            {
              if(
                i < guessed_args.arguments().size() &&
                tparams[i].get_bool(ID_ellipsis) &&
                (guessed_args.arguments()[i].id() == ID_unassigned ||
                 guessed_args.arguments()[i].type().id() == ID_unassigned))
              {
                guessed_args.arguments()[i] = exprt(ID_type, empty_typet());
              }
            }
          }

          if(guessed_args.has_unassigned() || guessed_args.has_conflict())
            continue;

          // [temp.variadic]/5: expand a deduced function parameter pack
          // in the guessed arguments into one positional argument per
          // element, matching the layout that template_mapt::build
          // expects when the specialization is instantiated (extra
          // positional arguments beyond the non-pack parameters are
          // collected into the pack).  Empty packs keep their existing
          // zero-length sentinel and are handled by build().
          {
            const auto &tparams =
              cpp_declaration.template_type().template_parameters();
            cpp_template_args_tct::argumentst expanded;
            for(std::size_t i = 0; i < guessed_args.arguments().size(); i++)
            {
              if(i < tparams.size() && tparams[i].get_bool(ID_ellipsis))
              {
                const irep_idt pid = tparams[i].id() == ID_type
                                       ? tparams[i].type().get(ID_identifier)
                                       : tparams[i].get(ID_identifier);
                auto pa_it = template_map.pack_args_map.find(pid);
                if(pa_it != template_map.pack_args_map.end())
                {
                  for(const auto &pt : pa_it->second)
                    expanded.push_back(exprt(ID_type, pt));
                  continue;
                }
                // [temp.variadic]/5 likewise for a NON-TYPE pack: its
                // deduced element VALUES live in pack_expr_map (e.g.
                // `_Ip = {0, 1}` from matching
                // `B<integer_sequence<unsigned long, _Ip...>>` against
                // `B<integer_sequence<unsigned long, 0, 1>>`, libc++'s
                // __bind_back_op).  Without splicing them, only the
                // single-element convenience entry survived and any
                // pack deduced to TWO or more values mis-instantiated
                // (sizeof... wrong / selection failed).
                auto pe_it = template_map.pack_expr_map.find(pid);
                if(pe_it != template_map.pack_expr_map.end())
                {
                  for(const auto &pe : pe_it->second)
                    expanded.push_back(pe);
                  continue;
                }
              }
              expanded.push_back(guessed_args.arguments()[i]);
            }
            guessed_args.arguments().swap(expanded);
          }

          // Evaluate requires clause (if present) with substituted args.
          // If the clause evaluates to false, skip this specialization.
          {
            const cpp_declarationt &spec_decl = to_cpp_declaration(s.type);
            const exprt &req_clause = static_cast<const exprt &>(
              spec_decl.template_type().find(ID_C_requires_clause));
            if(req_clause.is_not_nil() && req_clause.id() != ID_nil)
            {
              exprt req_copy = req_clause;
              template_map.apply(req_copy);
              // [temp.constr.atomic]/3: an unsatisfied atomic
              // constraint is a soft failure, not an ill-formed
              // program — treat typecheck errors here as SFINAE.
              bool satisfied = true;
              try
              {
                sfinae_contextt sfinae_guard{*this};
                typecheck_expr(req_copy);
                simplify(req_copy, *this);
                // N5008 [temp.constr.atomic]/3: the constraint is
                // unsatisfied when its (converted) value is false.  The
                // substituted clause may simplify to a NUMERIC zero
                // constant (a c-bool/int 0, e.g. libstdc++ <expected>'s
                // `requires is_void_v<_Tp>` with _Tp = int) rather than a
                // proper Boolean `false`; is_false() alone misses that,
                // wrongly selecting the void partial specialization for
                // every expected<_Tp, _Er>.
                if(req_copy.is_false() || req_copy.is_zero())
                  satisfied = false;
              }
              catch(...)
              {
                // Can't evaluate — treat as satisfied (backward compat)
              }
              if(!satisfied)
                continue;
            }

            // Check concept constraints on individual parameters.
            {
              const auto &spec_params =
                spec_decl.template_type().template_parameters();
              bool params_ok = true;
              for(std::size_t pi = 0; pi < spec_params.size() &&
                                      pi < full_args_tc.arguments().size();
                  ++pi)
              {
                const irep_idt &cc =
                  spec_params[pi].get("#C_concept_constraint");
                if(cc.empty())
                  continue;
                const auto concept_ids =
                  cpp_scopes.current_scope().lookup(cc, cpp_scopet::RECURSIVE);
                if(concept_ids.empty())
                  continue;
                const auto *concept_sym =
                  symbol_table.lookup((*concept_ids.begin())->identifier);
                if(!concept_sym || !concept_sym->type.get_bool(ID_is_template))
                  continue;
                const cpp_declarationt &concept_decl =
                  to_cpp_declaration(concept_sym->type);
                if(concept_decl.declarators().empty())
                  continue;
                exprt body = concept_decl.declarators()[0].value();
                if(body.is_nil())
                  continue;
                // Evaluate type_requirement nodes in the concept body.
                // Substitute the concept parameter with the actual type
                // and try to resolve each type requirement.
                template_mapt cmap;
                cpp_template_args_tct cargs;
                cargs.arguments().push_back(full_args_tc.arguments()[pi]);
                cmap.build(concept_decl.template_type(), cargs);
                // Create temporary symbols for requires-expression
                // parameters (e.g., requires(T t) { ++t; } needs 't').
                {
                  const irept &req_params = body.find("#requires_params");

                  for(const auto &param : req_params.get_sub())
                  {
                    irep_idt pname = param.get(ID_name);
                    if(pname.empty())
                      continue;
                    typet ptype =
                      static_cast<const typet &>(param.find(ID_type));
                    cmap.apply(ptype);
                    // [temp.constr.atomic]/3: substitution failure
                    // inside a requires-clause parameter type is a
                    // SFINAE failure (unsatisfied constraint), not
                    // a compilation error.
                    try
                    {
                      sfinae_contextt sfinae_guard{*this};
                      typecheck_type(ptype);
                    }
                    catch(...)
                    {
                    }
                    irep_idt id = "requires_param::" + id2string(pname);
                    if(!symbol_table.has_symbol(id))
                    {
                      symbolt param_sym{id, ptype, ID_cpp};
                      param_sym.base_name = pname;
                      param_sym.is_lvalue = true;
                      symbol_table.add(param_sym);
                    }
                    else
                    {
                      symbol_table.get_writeable_ref(id).type = ptype;
                    }
                    cpp_idt &scope_id =
                      cpp_scopes.current_scope().insert(pname);
                    scope_id.identifier = id;
                    scope_id.id_class = cpp_idt::id_classt::SYMBOL;
                  }
                }
                // Evaluate type_requirements by resolving types
                body.visit_pre(
                  [&](exprt &e)
                  {
                    // Handle nested concept references
                    // (cpp_name with template_args)
                    if(e.id() == ID_cpp_name && params_ok)
                    {
                      bool has_targs = false;
                      for(const auto &s : e.get_sub())
                        if(s.id() == ID_template_args)
                          has_targs = true;
                      if(has_targs)
                      {
                        exprt copy = e;
                        cmap.apply(copy);
                        // [temp.constr.atomic]/3: per-candidate
                        // concept check is SFINAE-guarded.
                        try
                        {
                          sfinae_contextt sfinae_guard{*this};
                          typecheck_expr(copy);
                          simplify(copy, *this);
                          if(copy.is_true())
                            e = typecast_exprt{true_exprt(), c_bool_type()};
                          else
                            params_ok = false;
                        }
                        catch(...)
                        {
                          params_ok = false;
                        }
                      }
                    }
                    if(e.id() == "type_requirement" && params_ok)
                    {
                      typet t = static_cast<const typet &>(e.find(ID_type_arg));
                      cmap.apply(t);
                      // [expr.prim.req.type]/1 + [temp.deduct]/8:
                      // a type requirement is satisfied iff the
                      // type-id is valid; substitution failure is
                      // a SFINAE failure.
                      try
                      {
                        sfinae_contextt sfinae_guard{*this};
                        typecheck_type(t);
                        e = typecast_exprt{true_exprt(), c_bool_type()};
                      }
                      catch(...)
                      {
                        params_ok = false;
                      }
                    }
                    // Simple requirement: check if expression type-checks
                    if(e.id() == "simple_requirement" && params_ok)
                    {
                      exprt expr_copy = to_unary_expr(e).op();
                      cmap.apply(expr_copy);
                      // [expr.prim.req.simple]/1 + [temp.deduct]/8:
                      // a simple requirement is satisfied iff the
                      // expression is valid; substitution failure
                      // is SFINAE.
                      try
                      {
                        sfinae_contextt sfinae_guard{*this};
                        typecheck_expr(expr_copy);
                        e = typecast_exprt{true_exprt(), c_bool_type()};
                      }
                      catch(...)
                      {
                        params_ok = false;
                      }
                    }
                    // Compound requirement: check expression type-checks
                    // and result type satisfies constraint
                    if(e.id() == "compound_requirement" && params_ok)
                    {
                      exprt expr_copy = to_unary_expr(e).op();
                      cmap.apply(expr_copy);
                      // [expr.prim.req.compound] + [temp.deduct]/8:
                      // a compound requirement checks that the
                      // expression is valid AND (if a trailing
                      // return-type constraint is present) that the
                      // result satisfies it.  Both checks are
                      // SFINAE-guarded.
                      bool ok = true;
                      try
                      {
                        sfinae_contextt sfinae_guard{*this};
                        typecheck_expr(expr_copy);
                        // Check return type constraint if present
                        const irept &constraint = e.find("#constraint");
                        if(constraint.is_not_nil())
                        {
                          // Per [expr.prim.req.compound], prepend
                          // decltype((expr)) to constraint template args.
                          typet result_type = expr_copy.type();
                          if(expr_copy.get_bool(ID_C_lvalue))
                            result_type = reference_type(result_type);
                          // Look up the concept and evaluate directly
                          irep_idt concept_name;
                          for(const auto &sub : constraint.get_sub())
                            if(sub.id() == ID_name)
                              concept_name = sub.get(ID_identifier);
                          if(!concept_name.empty())
                          {
                            auto cids = cpp_scopes.current_scope().lookup(
                              concept_name, cpp_scopet::RECURSIVE);
                            for(const auto *cid : cids)
                            {
                              const auto *csym =
                                symbol_table.lookup(cid->identifier);
                              if(!csym || !csym->type.get_bool(ID_is_template))
                                continue;
                              const auto &cd = to_cpp_declaration(csym->type);
                              if(cd.declarators().empty())
                                continue;
                              exprt cbody = cd.declarators()[0].value();
                              if(cbody.is_nil())
                                continue;
                              // Build template args: prepend result_type
                              // to the constraint's existing args
                              cpp_template_args_tct check_args;
                              exprt ta{ID_type};
                              ta.type() = result_type;
                              check_args.arguments().push_back(std::move(ta));
                              for(const auto &sub : constraint.get_sub())
                              {
                                if(sub.id() == ID_template_args)
                                {
                                  const auto &args_sub = sub.find(ID_arguments);
                                  for(const auto &a : args_sub.get_sub())
                                  {
                                    exprt arg_copy =
                                      static_cast<const exprt &>(a);
                                    cmap.apply(arg_copy);
                                    typecheck_type(arg_copy.type());
                                    check_args.arguments().push_back(
                                      std::move(arg_copy));
                                  }
                                }
                              }
                              template_mapt cmap2;
                              cmap2.build(cd.template_type(), check_args);
                              cmap2.apply(cbody);

                              typecheck_expr(cbody);
                              simplify(cbody, *this);
                              if(cbody.is_false())
                                ok = false;
                              break;
                            }
                          }
                        }
                      }
                      catch(...)
                      {
                        ok = false;
                      }
                      if(ok)
                        e = typecast_exprt{true_exprt(), c_bool_type()};
                      else
                        params_ok = false;
                    }
                  });
                if(!params_ok)
                  break;
                // Evaluate the concept body after type_requirement
                // and cpp_name nodes have been resolved.  Per
                // [temp.constr.constr]: the concept is satisfied
                // iff the body evaluates to `true` — substitution
                // failures are SFINAE failures.
                cmap.apply(body);
                bool old_suppress2 = suppress_elaborate;
                suppress_elaborate = false;
                try
                {
                  sfinae_contextt sfinae_guard{*this};
                  typecheck_expr(body);
                  simplify(body, *this);
                  if(body.is_false())
                    params_ok = false;
                }
                catch(...)
                {
                  params_ok = false;
                }
                suppress_elaborate = old_suppress2;
              }
              if(!params_ok)
                continue;
            }
          }

          // Typecheck the partial specialization args with the guessed
          // values, using the primary template for type context.
          // If typechecking fails (e.g., accessing a member of a
          // non-class type), treat it as a substitution failure
          // (SFINAE) and skip this specialization.
          cpp_template_args_tct partial_specialization_args_tc;
          bool sfinae_failed = false;
          {
            // Per [temp.inst]/1 + [temp.deduct]/8: partial
            // specialization matching uses template-argument
            // deduction, so substitution failure is SFINAE.
            // Suppress eager elaboration to avoid instantiating
            // unused branches (e.g. conditional_t's false branch).
            bool old_suppress = suppress_elaborate;
            suppress_elaborate = true;
            // [temp.arg.explicit]/4 note 1 + [temp.variadic]/4: a trailing
            // parameter pack deduced to an empty sequence contributes zero
            // arguments.  When the specialization pattern has MORE arguments
            // than the actual (`<H, T...>` matched against `<3>`), the extra
            // trailing pack-expansion arguments are those empty packs; drop
            // them from the pattern before re-type-checking so a NON-type pack
            // expansion `T...` is not evaluated as an unassigned scalar (which
            // throws).  This mirrors the trailing-empty-pack trim applied to
            // the type-checked result below.
            cpp_template_args_non_tct trimmed_psa = partial_specialization_args;
            {
              auto &in_args = trimmed_psa.arguments();
              while(in_args.size() > full_args_tc.arguments().size() &&
                    !in_args.empty())
              {
                const auto &last = in_args.back();
                if(
                  last.get_bool(ID_ellipsis) ||
                  last.type().get_bool(ID_ellipsis))
                  in_args.pop_back();
                else
                  break;
              }
            }
            try
            {
              sfinae_contextt sfinae_guard{*this};
              partial_specialization_args_tc = typecheck_template_args(
                type.source_location(), primary_template, trimmed_psa);
            }
            catch(...)
            {
              sfinae_failed = true;
            }
            suppress_elaborate = old_suppress;
          }
          if(sfinae_failed)
            continue;

          // Strip ellipsis flags from cpp_declaration declarators in
          // code type arguments (variadic pack residue).
          for(auto &arg : partial_specialization_args_tc.arguments())
          {
            if(arg.id() != ID_type || arg.type().id() != ID_code)
              continue;
            for(auto &param : arg.type().add(ID_parameters).get_sub())
            {
              if(param.id() != ID_cpp_declaration)
                continue;
              for(auto &decl :
                  static_cast<cpp_declarationt &>(param).declarators())
                decl.remove(ID_ellipsis);
            }
          }

          // Remove trailing pack expansion args from the type-checked
          // partial specialization args that correspond to empty packs
          // in the original (non-type-checked) partial specialization.
          {
            const auto &orig_args = partial_specialization_args.arguments();
            auto &tc_args = partial_specialization_args_tc.arguments();
            while(tc_args.size() > full_args_tc.arguments().size() &&
                  !tc_args.empty() && tc_args.size() <= orig_args.size())
            {
              std::size_t idx = tc_args.size() - 1;
              const auto &orig = orig_args[idx];
              if(
                orig.get_bool(ID_ellipsis) || orig.type().get_bool(ID_ellipsis))
              {
                tc_args.pop_back();
              }
              else
                break;
            }
          }

          // A function-type template argument may carry a parameter's
          // reference/pointer/array part either on the parameter
          // declaration's type or on its declarator: the parser places
          // it on the declarator, whereas substituting a deduced
          // argument places it on the type.  Normalise both forms by
          // merging each cpp_declaration parameter's declarator into its
          // type, so structurally-equivalent function types (e.g. the
          // requested `R(const T&)` and the deduced one) compare equal.
          auto normalize_code_args =
            [](cpp_template_args_tct args) -> cpp_template_args_tct
          {
            for(auto &arg : args.arguments())
            {
              if(arg.id() != ID_type || arg.type().id() != ID_code)
                continue;
              for(auto &param : arg.type().add(ID_parameters).get_sub())
              {
                if(param.id() != ID_cpp_declaration)
                  continue;
                auto &decl = static_cast<cpp_declarationt &>(param);
                if(decl.declarators().empty())
                  continue;
                typet merged =
                  decl.declarators().front().merge_type(decl.type());
                decl.type() = merged;
                decl.declarators().front().type().make_nil();
              }
            }
            return args;
          };

          const cpp_template_args_tct norm_ps =
            normalize_code_args(partial_specialization_args_tc);
          const cpp_template_args_tct norm_full =
            normalize_code_args(full_args_tc);

          if(norm_ps.arguments() == norm_full.arguments())
          {
            // operator== on irept ignores #-prefixed attributes like
            // C_constant and C_volatile. Check them recursively on
            // the type tree so that e.g. const T* and T* partial
            // specializations are correctly distinguished.
            bool qualifiers_match = true;
            for(std::size_t j = 0; j < norm_ps.arguments().size(); j++)
            {
              const exprt &p = norm_ps.arguments()[j];
              const exprt &f = norm_full.arguments()[j];
              if(p.id() == ID_type)
              {
                if(!qualifiers_match_recursively(p.type(), f.type()))
                {
                  qualifiers_match = false;
                  break;
                }
              }
            }
            if(!qualifiers_match)
              continue;
            // Check if this specialization is more specialized than
            // the current best match. A specialization is more
            // specialized if its pattern has more constrained
            // arguments (e.g., pack<Rp...> vs plain Rp).
            if(best_match == &primary_template)
            {
              best_match = &s;
              best_spec_args = guessed_args;
            }
            else
            {
              const cpp_declarationt &best_decl =
                to_cpp_declaration(best_match->type);
              const cpp_template_args_non_tct &best_partial_args =
                best_decl.partial_specialization_args();

              // Count non-trivial arguments. A cpp_name with template
              // args (e.g., pack<Rp...>) counts as constrained.
              auto count_constrained = [](const cpp_template_args_non_tct &args)
              {
                std::size_t count = 0;
                for(const auto &arg : args.arguments())
                {
                  const irept *a = &arg;
                  if(a->id() == ID_type)
                    a = &arg.type();
                  if(a->id() == ID_ambiguous)
                    a = &a->find(ID_type);

                  if(a->id() != ID_cpp_name)
                  {
                    count++;
                  }
                  else
                  {
                    for(const auto &sub : a->get_sub())
                      if(sub.id() == ID_template_args)
                      {
                        count++;
                        break;
                      }
                  }
                }
                return count;
              };

              if(
                count_constrained(partial_specialization_args) >
                count_constrained(best_partial_args))
              {
                best_match = &s;
                best_spec_args = guessed_args;
              }
              // Prefer specialization with fewer args (more specific)
              // when constraint counts are equal.
              else if(
                count_constrained(partial_specialization_args) ==
                  count_constrained(best_partial_args) &&
                partial_specialization_args.arguments().size() <
                  best_partial_args.arguments().size())
              {
                best_match = &s;
                best_spec_args = guessed_args;
              }
              // N5008 [temp.class.spec.match]/2 + [temp.constr.order]: when
              // the argument patterns are equally specialized, the more
              // CONSTRAINED specialization is selected, determined by
              // constraint subsumption -- not by any counting heuristic.
              // libstdc++'s __iterator_traits::__cat has three partial
              // specializations with the same pattern whose requires-clauses
              // form a subsumption chain (__cpp17_input_iterator subsumed by
              // __cpp17_fwd_iterator subsumed by __cpp17_randacc_iterator
              // conjunctions); all three are satisfied for a random-access
              // iterator and only subsumption picks the right one.  The
              // previous count-based tie-break fell through to FIRST-SEEN in
              // the pointer-ordered id_set (std::set<cpp_idt*>), making the
              // selection ASLR-dependent (run-to-run flakiness; determinize
              // with `setarch -R` when debugging).
              else if(
                count_constrained(partial_specialization_args) ==
                  count_constrained(best_partial_args) &&
                partial_specialization_args.arguments().size() ==
                  best_partial_args.arguments().size())
              {
                if(template_constraint_strictly_subsumes(
                     symbol_table, cpp_declaration, best_decl))
                {
                  best_match = &s;
                  best_spec_args = guessed_args;
                }
                else if(
                  !template_constraint_strictly_subsumes(
                    symbol_table, best_decl, cpp_declaration) &&
                  s.name < best_match->name)
                {
                  // Constraints are incomparable (or both unconstrained):
                  // no standard-mandated winner among the satisfied
                  // candidates.  Break the tie DETERMINISTICALLY by symbol
                  // name so the selection cannot depend on the iteration
                  // order of the pointer-keyed id_set.
                  best_match = &s;
                  best_spec_args = guessed_args;
                }
              }
            }
          }
        }
      }
    }

    // Catch instantiation errors to preserve partially-completed types.
    // Template instantiation creates the struct body (components) first,
    // then processes method bodies which may fail for system headers.
    // Without catching, the exception propagates and the caller sees
    // the type as incomplete even though the struct body is complete.
    // C++20: evaluate requires clause on the selected specialization.
    if(!best_match->type.get(ID_specialization_of).empty())
    {
      const cpp_declarationt &spec_decl = to_cpp_declaration(best_match->type);
      const exprt &req_clause = static_cast<const exprt &>(
        spec_decl.template_type().find(ID_C_requires_clause));
      if(req_clause.is_not_nil() && req_clause.id() != ID_nil)
      {
        // Build parameter name -> actual type mapping
        const auto &params = spec_decl.template_type().template_parameters();
        std::map<irep_idt, typet> param_map;
        for(std::size_t i = 0;
            i < params.size() && i < full_args_tc.arguments().size();
            ++i)
        {
          if(params[i].id() == ID_type)
          {
            const std::string id_str =
              id2string(params[i].type().get(ID_identifier));
            auto pos = id_str.rfind("::");
            irep_idt pname = pos != std::string::npos
                               ? irep_idt{id_str.substr(pos + 2)}
                               : irep_idt{id_str};
            if(!pname.empty())
              param_map[pname] = full_args_tc.arguments()[i].type();
          }
        }

        // Resolve a type from a cpp_name or type_exprt
        std::function<typet(const irept &)> resolve_type =
          [&](const irept &node) -> typet
        {
          if(node.id() == ID_type)
            return static_cast<const type_exprt &>(
                     static_cast<const exprt &>(node))
              .type();
          if(node.id() == ID_cpp_name)
          {
            for(const auto &s : node.get_sub())
              if(s.id() == ID_name)
              {
                auto it = param_map.find(s.get(ID_identifier));
                if(it != param_map.end())
                  return it->second;
              }
          }
          return typet{};
        };

        // Evaluate a requires clause expression with substituted types
        std::function<int(const irept &)> eval = [&](const irept &node) -> int
        {
          // -1 = can't evaluate, 0 = false, 1 = true
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
            for(const auto &sub : node.get_sub())
            {
              int v = eval(sub);
              if(v == 1)
                return 1;
              if(v == -1)
                return -1;
            }
            return 0;
          }
          if(node.id() == ID_not)
          {
            if(node.get_sub().empty())
              return -1;
            int v = eval(node.get_sub()[0]);
            return v == -1 ? -1 : (v == 0 ? 1 : 0);
          }
          // side_effect(statement=function_call) with cpp_name as function
          if(node.id() == ID_side_effect)
          {
            const auto &subs = node.get_sub();
            if(subs.size() >= 2 && subs[0].id() == ID_cpp_name)
            {
              irep_idt fname;
              for(const auto &s : subs[0].get_sub())
                if(s.id() == ID_name)
                  fname = s.get(ID_identifier);
              // Get the argument type
              const auto &args = subs[1].get_sub();
              if(args.empty())
                return -1;
              // For __remove_pointer, evaluate the inner call first
              typet arg_type;
              if(args[0].id() == ID_side_effect)
              {
                // Nested call like __remove_pointer(T)
                irep_idt inner_fname;
                const auto &inner_subs = args[0].get_sub();
                if(inner_subs.size() >= 2 && inner_subs[0].id() == ID_cpp_name)
                {
                  for(const auto &s : inner_subs[0].get_sub())
                    if(s.id() == ID_name)
                      inner_fname = s.get(ID_identifier);
                  const auto &inner_args = inner_subs[1].get_sub();
                  if(!inner_args.empty())
                  {
                    typet inner_type = resolve_type(inner_args[0]);
                    if(inner_type.is_nil())
                      return -1;
                    if(inner_fname == "__remove_pointer")
                    {
                      if(inner_type.id() == ID_pointer)
                        arg_type = to_pointer_type(inner_type).base_type();
                      else
                        return -1;
                    }
                    else
                      return -1;
                  }
                  else
                    return -1;
                }
                else
                  return -1;
              }
              else
              {
                arg_type = resolve_type(args[0]);
              }
              if(arg_type.is_nil())
                return -1;
              if(fname == "__is_pointer")
                return arg_type.id() == ID_pointer ? 1 : 0;
              if(fname == "__is_integral")
                return (arg_type.id() == ID_signedbv ||
                        arg_type.id() == ID_unsignedbv ||
                        arg_type.id() == ID_bool || arg_type.id() == ID_c_bool)
                         ? 1
                         : 0;
              if(fname == "__is_signed")
                return arg_type.id() == ID_signedbv ? 1 : 0;
            }
          }
          return -1;
        };

        int result = eval(req_clause);
        if(result == 0)
        {
          // Requires clause is false — try other specializations
          const irep_idt &prim_name =
            best_match->type.get(ID_specialization_of);
          const auto *primary = symbol_table.lookup(prim_name);
          if(primary)
          {
            const symbolt *fallback = primary;
            // Search for a satisfied specialization
            cpp_scopet *ts = id_map_lookup(cpp_scopes, prim_name);
            if(ts)
            {
              cpp_scopet &scope = ts->get_parent();
              cpp_scopet::id_sett id_set =
                scope.lookup(primary->base_name, cpp_scopet::SCOPE_ONLY);
              for(const auto *id_ptr : id_set)
              {
                const symbolt &s = lookup(id_ptr->identifier);
                if(s.type.get(ID_specialization_of).empty())
                  continue;
                if(&s == best_match)
                  continue;
                const cpp_declarationt &sd = to_cpp_declaration(s.type);
                const exprt &rc = static_cast<const exprt &>(
                  sd.template_type().find(ID_C_requires_clause));
                if(rc.is_nil() || rc.id() == ID_nil)
                  continue;
                int rv = eval(rc);
                if(rv == 1)
                {
                  fallback = &s;
                  break;
                }
              }
            }
            best_match = fallback;
            best_spec_args = full_args;
          }
        }
      }
    }

    // Re-check: the symbol may have been elaborated by a recursive
    // call during the specialization matching above.  Per the
    // standard, a class template specialization that is already
    // complete should not be re-instantiated.
    {
      const symbolt &sym_now = lookup(to_tag_type(type));
      if(
        (sym_now.type.id() == ID_struct || sym_now.type.id() == ID_union) &&
        !to_struct_union_type(sym_now.type).components().empty() &&
        !to_struct_union_type(sym_now.type).is_incomplete() &&
        !dropped_base_now_complete(sym_now.type))
      {
        return;
      }
    }

    // N5008 [temp.inst]/1, [temp.point]: only a *defined* class template can be
    // implicitly instantiated.  If the selected template (the primary template
    // or the partial specialization chosen above) has so far only been
    // forward-declared -- no class body has been seen for it, i.e. it is not in
    // defined_class_templates -- defer: leave the specialization incomplete
    // rather than fabricating a spurious empty-but-complete class.  Finalising
    // such an instance drops its link back to the template, so the members
    // added by a later definition would be permanently masked.  The
    // specialization is elaborated correctly once the definition is available
    // and its completeness is actually required.
    //
    // The check is on best_match (post specialization matching), not on the
    // primary template: for e.g. std::function only the partial specialization
    // function<R(Args...)> is defined while the primary function<T> is
    // bodyless, so keying off the primary would wrongly defer it.
    if(
      best_match->type.id() == ID_cpp_declaration &&
      defined_class_templates.find(best_match->name) ==
        defined_class_templates.end())
    {
      return;
    }

    // A completed instance whose base was dropped cannot be repaired
    // in place (conversion of an already-complete symbol is a no-op):
    // reset it to the INCOMPLETE state so the re-instantiation below
    // runs the ordinary incomplete-to-complete completion, rebuilding
    // members AND bases against the now-complete base type.
    {
      symbolt *sym_ptr = symbol_table.get_writeable(symbol.name);
      if(
        sym_ptr != nullptr &&
        (sym_ptr->type.id() == ID_struct || sym_ptr->type.id() == ID_union) &&
        dropped_base_now_complete(sym_ptr->type) &&
        !to_struct_union_type(sym_ptr->type).is_incomplete())
      {
        // The first (degenerate) elaboration may have CONVERTED member
        // bodies against the base-less layout (e.g. a constructor whose
        // base mem-initializer matched no base and became an empty
        // block).  The re-instantiation below re-creates the member
        // declarations, but the declarator converter REUSES existing
        // symbols including their stale values; erase the instance's
        // member symbols (methods and their locals) so they are rebuilt
        // fresh against the repaired layout.
        std::vector<irep_idt> to_erase;
        // symbol.name is '[ns::]tag-X<...>'; member names are
        // '[ns::]X<...>::...' -- strip the "tag-" that starts the LAST
        // top-level component (position 0 or right after "::"), NOT one
        // inside the template argument list (rfind matched
        // 'tag-ssa_exprt' inside 'tag-renamedt<tag-ssa_exprt>' and the
        // erase never fired, silently keeping the stale members).
        std::string inst_prefix = id2string(symbol.name);
        std::size_t comp_start = 0;
        {
          std::size_t depth = 0;
          for(std::size_t ci = 0; ci + 1 < inst_prefix.size(); ++ci)
          {
            if(inst_prefix[ci] == '<')
              ++depth;
            else if(inst_prefix[ci] == '>' && depth > 0)
              --depth;
            else if(
              depth == 0 && inst_prefix[ci] == ':' &&
              inst_prefix[ci + 1] == ':')
              comp_start = ci + 2;
          }
        }
        if(inst_prefix.compare(comp_start, 4, "tag-") == 0)
          inst_prefix.erase(comp_start, 4);
        inst_prefix += "::";
        for(const auto &entry : symbol_table.symbols)
        {
          const std::string n = id2string(entry.first);
          if(n.compare(0, inst_prefix.size(), inst_prefix) == 0)
            to_erase.push_back(entry.first);
        }
        // The drain queue holds POINTERS into the symbol table; purge
        // entries for the members about to be erased BEFORE removing
        // them (afterwards the pointers dangle).
        {
          const std::set<irep_idt> erase_set(to_erase.begin(), to_erase.end());
          method_bodies.remove_if(
            [&](const method_bodyt &mb)
            {
              return mb.method_symbol != nullptr &&
                     erase_set.count(mb.method_symbol->name) != 0;
            });
        }
        for(const auto &n : to_erase)
        {
          methods_seen.erase(n);
          deferred_typechecking.erase(n);
          deferred_method_bodies.erase(n);
          symbol_table.remove(n);
        }
        to_struct_union_type(sym_ptr->type).components().clear();
        sym_ptr->type.remove("#dropped_incomplete_base");
        to_struct_union_type(sym_ptr->type).make_incomplete();
        sym_ptr->type.set(ID_template_class_instance, true);
      }
    }

    instantiate_template(
      type.source_location(), *best_match, best_spec_args, full_args);
  }
}

/// Find and instantiate the out-of-line definition body of a class-template
/// instance member function, selected by **signature** (parameter arity), not
/// by base name.
///
/// libstdc++ overloads several members on the same name (e.g.
/// `basic_string::_M_construct` has a `(size_type, _CharT)` fill overload and
/// the `(_InputIterator, _InputIterator, tag)` range overloads).  The body of
/// such a member is kept, in parsed form, in a primary template's
/// `ID_template_methods`.  Matching it by base name alone can attach the
/// **wrong** overload's body to a member symbol (observed: the input-iterator
/// `_M_construct` body, which references `__beg`, ends up on the fill
/// `_M_construct(size_type, char)` member, so its conversion fails with
/// "symbol '__beg' is unknown" and the member silently becomes a no-op).
///
/// This routine returns the substituted body of the **unique** out-of-line
/// definition whose (non-`this`) parameter count matches \p member, or an
/// empty optional if there is no match or the match is ambiguous.  Only
/// regular members (whose template parameters are exactly the enclosing
/// class's) are handled; member function templates are left to their own
/// instantiation path.
///
/// Grounded in N5008 [temp.over]/[over.match]: the definition that belongs to
/// a member is the one whose function signature matches it, independent of
/// the parameter *names* used in the out-of-line definition ([dcl.fct]/3).
///
/// \param member: the realized instance member function symbol
/// \param [out] param_names: on success, the out-of-line definition's
///   parameter base names (excluding `this`), to be adopted by the member so
///   the body's parameter references resolve ([dcl.fct]/3)
/// \return the substituted out-of-line body, or empty optional
std::optional<exprt> cpp_typecheckt::instantiate_matching_member_body(
  const symbolt &member,
  std::vector<irep_idt> &param_names)
{
  if(member.type.id() != ID_code)
    return {};
  const irep_idt &class_id = member.type.get(ID_C_member_name);
  if(class_id.empty())
    return {};
  const symbolt *class_sym = symbol_table.lookup(class_id);
  if(class_sym == nullptr)
    return {};
  const irept &c_template = class_sym->type.find(ID_C_template);
  const irept &c_args = class_sym->type.find(ID_C_template_arguments);
  if(c_template.is_nil() || c_args.is_nil())
    return {};
  const auto &spec_args = static_cast<const cpp_template_args_tct &>(c_args);

  // (non-this) parameter count of the member
  const auto &mparams = to_code_type(member.type).parameters();
  std::size_t member_param_count = mparams.size();
  if(!mparams.empty() && mparams.front().get_this())
    --member_param_count;

  // Source line of the body currently attached to the member (the body comes
  // from some out-of-line definition; this is used to identify which
  // definition it originates from).
  const irep_idt current_body_line = member.value.source_location().get_line();

  // The base name of the member's own class (e.g. `basic_string` from
  // `std::__cxx11::tag-basic_string<char,...>`): a candidate definition
  // must belong to THIS class template.  Same-named members of other
  // templates (basic_string_view::rfind vs basic_string::rfind) are not
  // this member's definition ([class.mfct]/1: the definition of a member
  // function is a member of the class it is declared in), and matching
  // them by base name attaches a body whose parameter names and
  // semantics belong elsewhere.
  std::string class_base;
  {
    std::string cn = id2string(class_id);
    std::size_t clt = cn.find('<');
    if(clt != std::string::npos)
      cn.erase(clt);
    std::size_t csep = cn.rfind("::");
    if(csep != std::string::npos)
      cn.erase(0, csep + 2);
    if(cn.compare(0, 4, "tag-") == 0)
      cn.erase(0, 4);
    class_base = cn;
  }

  const cpp_declarationt *match = nullptr;
  bool current_def_found = false;
  std::size_t current_def_param_count = 0;
  for(const auto &tsp : symbol_table.symbols)
  {
    if(!tsp.second.type.get_bool(ID_is_template) || tsp.second.value.is_nil())
      continue;
    // Owner check (see class_base above).
    bool owner_matches = false;
    {
      const std::string tid = id2string(tsp.first);
      std::size_t tpos = tid.rfind("template.");
      if(tpos != std::string::npos)
      {
        std::string owner = tid.substr(tpos + 9);
        std::size_t olt = owner.find('<');
        if(olt != std::string::npos)
          owner.erase(olt);
        owner_matches = owner == class_base;
      }
    }
    const exprt &tms =
      static_cast<const exprt &>(tsp.second.value.find(ID_template_methods));
    for(const auto &tm : tms.operands())
    {
      const cpp_declarationt &md =
        static_cast<const cpp_declarationt &>(static_cast<const irept &>(tm));
      if(md.declarators().empty())
        continue;
      if(md.declarators()[0].name().get_base_name() != member.base_name)
        continue;
      const exprt &md_value =
        static_cast<const exprt &>(md.declarators()[0].find(ID_value));
      if(md_value.is_nil())
        continue;
      const std::size_t md_param_count =
        md.declarators()[0].type().find(ID_parameters).get_sub().size();
      // Identify the definition the currently-attached body came from, by
      // source line, to learn its parameter arity.  This identification is
      // deliberately NOT owner-filtered: the wrongly-attached body may come
      // from ANOTHER class's same-named member (string_view.tcc's rfind on
      // basic_string<char>::rfind).
      if(
        !current_body_line.empty() &&
        md_value.source_location().get_line() == current_body_line)
      {
        current_def_found = true;
        current_def_param_count = md_param_count;
      }
      if(!owner_matches)
        continue;
      // Only regular members (template parameters == enclosing class's);
      // member function templates are instantiated on their own path.
      if(
        md.template_type().template_parameters().size() >
        spec_args.arguments().size())
        continue;
      // Signature match by (non-this) parameter arity.
      if(md_param_count != member_param_count)
        continue;
      if(match != nullptr)
        return {}; // ambiguous — do not guess
      match = &md;
    }
  }

  // Only repair a *genuine* wrong-overload attachment: the currently-attached
  // body must be identifiable as coming from a definition whose parameter
  // arity differs from this member's.  This distinguishes the fill
  // _M_construct case (arity-3 input-iterator body wrongly attached to the
  // arity-2 fill member) from a same-arity member whose own body merely fails
  // to convert for an unrelated reason -- repairing the latter would convert
  // a body that should be left alone and could surface latent modelling gaps.
  if(!current_def_found || current_def_param_count == member_param_count)
    return {};

  if(match == nullptr)
    return {};

  // Collect the definition's parameter base names ([dcl.fct]/3): the body
  // refers to these, so the member must adopt them.
  param_names.clear();
  for(const auto &p :
      match->declarators()[0].type().find(ID_parameters).get_sub())
  {
    const auto &pd = static_cast<const cpp_declarationt &>(p);
    if(pd.declarators().empty())
      param_names.push_back(irep_idt{});
    else
      param_names.push_back(pd.declarators().front().name().get_base_name());
  }

  exprt body =
    static_cast<const exprt &>(match->declarators()[0].find(ID_value));
  cpp_saved_template_mapt saved_map(template_map);
  template_map.build(match->template_type(), spec_args);
  template_map.apply(body);
  return body;
}

/// Queue the already-bodied (inline) deferred member functions of a realized
/// class-template instance for type-checking.
///
/// During class-body elaboration the inline member functions of a template
/// instance are parked in `deferred_typechecking` because their parent scope
/// is a template scope (see `typecheck_compound_declarator`).  Instances
/// realized through `instantiate_template` drain that queue inline; but an
/// instance completed through the incomplete-to-complete swap in
/// `typecheck_compound_type` -- in particular the explicitly/extern-
/// instantiated `std::__cxx11::basic_string<char>` shipped by libstdc++ --
/// never reaches that loop, so its member bodies would otherwise be discarded
/// (made nil) by `clean_up()`, turning the character-copy helpers
/// `_S_copy_chars`/`_S_copy` into no-ops.
///
/// Each matching member that already carries a body is routed through
/// `add_method_body`, which rebuilds the class template map from the
/// instance's `ID_C_template` / `ID_C_template_arguments` and queues the body
/// for `typecheck_method_bodies`.  Members with a nil in-class body
/// (out-of-line definitions kept in a primary template's `template_methods`)
/// are deliberately left untouched here: fetching them by base name is
/// overload-ambiguous and converting them eagerly destabilises unrelated
/// standard-library classes, so they continue to be handled by the existing
/// odr-use-driven paths.
///
/// Grounded in N5008 [temp.inst]/4 and [temp.inst] Note 4: an inline member
/// that is the subject of an explicit instantiation declaration is not a
/// declared specialization and must still be implicitly instantiated when
/// odr-used.  CBMC links no external library that could supply the
/// definition, so it must instantiate it here.
///
/// The function is idempotent: it erases each handled name from
/// `deferred_typechecking`, and `add_method_body` guards against double
/// queuing via `methods_seen`.
///
/// \param class_id: symbol-table identifier of the realized class instance
///   (the tag-prefixed name, e.g. `…::tag-basic_string<char,…>`)
void cpp_typecheckt::queue_deferred_methods_of_instance(
  const irep_idt &class_id)
{
  std::string class_name = id2string(class_id);
  // Strip the "tag-" marker that precedes the class name in the symbol-table
  // id of a class-template instantiation.  The id has the form
  //   `[ns1::...::nsN::]tag-Name<args>`
  // where `args` may themselves contain `::` (e.g. a namespaced argument such
  // as `std::tag-char_traits<char>`).  The `tag-` to strip is therefore the
  // token immediately after the last `::` that precedes the template-argument
  // list (the first `<`), not after the last `::` in the whole string.  The
  // deferred method ids store the class name without that `tag-` token (e.g.
  // `ns::Name<args>::method(this)`), so we bring class_name into the same
  // shape for the substring match below.
  std::size_t lt = class_name.find('<');
  std::size_t search_end = lt == std::string::npos ? std::string::npos : lt;
  std::size_t sep = class_name.rfind("::", search_end);
  std::size_t tag_pos = sep != std::string::npos ? sep + 2 : 0;
  if(class_name.compare(tag_pos, 4, "tag-") == 0)
    class_name.erase(tag_pos, 4);
  class_name += "::";

  std::vector<irep_idt> to_queue;
  for(const auto &d : deferred_typechecking)
  {
    if(id2string(d).find(class_name) != std::string::npos)
      to_queue.push_back(d);
  }

  for(const auto &d : to_queue)
  {
    auto *sym = symbol_table.get_writeable(d);
    if(sym == nullptr || sym->type.id() != ID_code)
      continue;
    // Inline members only: skip members whose in-class body is nil
    // (out-of-line, kept in template_methods).  Those definitions are
    // included AFTER the explicit instantiation declaration that created
    // this instance (libstdc++'s bits/basic_string.tcc at the bottom of
    // <string>); recording the instance in the owning template's
    // `instantiated_with` (see typecheck_compound_type's swap-completion)
    // makes typecheck_class_template_member replay them for this
    // instance when they arrive.
    if(sym->value.is_nil())
      continue;
    deferred_typechecking.erase(d);
    add_method_body(sym);
  }
}

/// Instantiate a template with the given arguments.
///
/// Implements [temp.inst]: implicit instantiation of class and function
/// templates.  For class templates, creates the class symbol with
/// substituted template arguments and processes the class body
/// ([temp.mem.func], [temp.mem.class], [temp.static]).  For function
/// templates, creates the function symbol with substituted types.
///
/// Template argument substitution follows [temp.deduct.type]: the
/// template_map is used to replace template parameters with their
/// deduced or explicitly specified values.
///
/// \param source_location: location of the instantiation
/// \param template_symbol: the template being instantiated
/// \param specialization_template_args: typechecked template arguments
/// \param full_template_args: full set of template arguments
/// \param specialization: optional explicit specialization type
#define MAX_DEPTH 50

/// Decide whether two template declarations name the *same* template -- i.e.
/// whether \p candidate could be the definition of a forward declaration
/// \p forward.  A forward declaration and its definition necessarily share an
/// identical signature ([temp.over.link], [basic.link]/11): the same template
/// parameter list and the same function parameter-type list.  Distinct
/// overloads of a function template differ in at least one of these -- e.g.
/// the `std::swap` overloads differ in template-parameter arity (generic
/// `swap(_Tp&,_Tp&)` has one type parameter; pair `swap(pair<_T1,_T2>&,...)`
/// has two), while the 3- and 4-iterator `std::equal` overloads share a
/// two-parameter template list but differ in function-parameter arity.
/// Matching a forward-declared template to its definition by base name alone
/// therefore risks binding the wrong overload's parameter list to the deduced
/// arguments (leaving parameters unbound and aborting the instantiation), so
/// require both the template-parameter list (arity + each parameter's
/// type/non-type kind) and the function-parameter arity to agree.
bool cpp_typecheckt::function_template_signatures_equivalent(
  const cpp_declarationt &forward,
  const cpp_declarationt &candidate)
{
  const auto &fp = forward.template_type().template_parameters();
  const auto &cp = candidate.template_type().template_parameters();
  if(fp.size() != cp.size())
    return false;
  // N5008 [temp.over.link]/6-7: equivalence requires EQUIVALENT
  // constraints -- two templates differing only in a type-constraint
  // (`template <Integral T>` vs `template <SignedIntegral T>`) or a
  // requires-clause declare DISTINCT (overloadable, partially-ordered)
  // entities.
  if(
    forward.template_type().find(ID_C_requires_clause) !=
    candidate.template_type().find(ID_C_requires_clause))
    return false;
  for(std::size_t i = 0; i < fp.size(); ++i)
  {
    if(fp[i].get("#C_concept_constraint") != cp[i].get("#C_concept_constraint"))
      return false;
    // A type parameter is represented with id ID_type; a non-type parameter
    // is a value declaration.  Mixing the two is a different template.
    if((fp[i].id() == ID_type) != (cp[i].id() == ID_type))
      return false;
    // N5008 [temp.over.link]/6: parameter PACK-ness and a non-type
    // parameter's declared type are part of the signature, too --
    // `template<long, class...> get(int)` must not redirect to
    // `template<int, class> get(void)` (libc++'s <__fwd/get.h>
    // declares the tuple/pair/array `get` family side by side, so a
    // loose match binds the wrong overload's parameter list and the
    // instantiated function loses its parameters).
    if(fp[i].get_bool(ID_ellipsis) != cp[i].get_bool(ID_ellipsis))
      return false;
    if(
      fp[i].id() != ID_type &&
      cpp_type2name(fp[i].type()) != cpp_type2name(cp[i].type()))
      return false;
  }
  if(forward.declarators().empty() || candidate.declarators().empty())
    return true;
  // Compare the function-parameter lists, distinguishing overloads that
  // share a template-parameter list (e.g. the 3- and 4-iterator
  // std::equal, or by-index vs by-type `get` overloads with the same
  // arity).  Parameter TYPES spelled in terms of template parameters
  // compare by their parse-level name only (positional normalization is
  // not attempted); differing spellings of the same type would wrongly
  // fail this redirect, which is conservative -- the forward declaration
  // then simply has no body, as before the redirect existed.
  const typet f_type = forward.declarators().front().merge_type(forward.type());
  const typet c_type =
    candidate.declarators().front().merge_type(candidate.type());
  const irept &f_params = f_type.find(ID_parameters);
  const irept &c_params = c_type.find(ID_parameters);
  if(f_params.is_not_nil() || c_params.is_not_nil())
  {
    // [dcl.fct]/4: a parameter list `(void)` declares NO parameters --
    // count it as zero, or `get(int)` matches `get(void)` by "arity".
    const auto arity = [](const irept &params) -> std::size_t
    {
      const auto &sub = params.get_sub();
      if(sub.size() == 1 && sub.front().id() == ID_cpp_declaration)
      {
        const auto &d = static_cast<const cpp_declarationt &>(sub.front());
        if(
          d.type().id() == ID_void &&
          (d.declarators().empty() ||
           (d.declarators().size() == 1 && d.declarators()[0].type().is_nil() &&
            d.declarators()[0].name().id() == ID_nil)))
          return 0;
      }
      return sub.size();
    };
    if(arity(f_params) != arity(c_params))
      return false;

    // Compare the parameter TYPES, too: `get(tuple<_Tp...>)` is a
    // different signature from `get(tuple<>)` (third cvise harvest).
    // References to the templates' OWN parameters are normalised to
    // their POSITION (`#0`, `#1`, ...) so the same signature spelled
    // with differently NAMED parameters still matches -- libc++'s
    // <__fwd/*.h> declarations must keep redirecting to their
    // definitions.  Structurally different parameter types then
    // compare unequal; a wrongly-failed redirect is conservative (the
    // declaration stays bodyless, the pre-redirect behaviour).
    const auto normalized =
      [](const irept &params, const template_typet &ttype) -> std::string
    {
      std::map<std::string, std::string> rename;
      std::size_t idx = 0;
      for(const auto &tp : ttype.template_parameters())
      {
        const irep_idt id = tp.id() == ID_type ? tp.type().get(ID_identifier)
                                               : tp.get(ID_identifier);
        const std::string ids = id2string(id);
        const auto pos = ids.rfind("::");
        const std::string short_name =
          pos != std::string::npos ? ids.substr(pos + 2) : ids;
        if(!short_name.empty())
          rename[short_name] = "#" + std::to_string(idx);
        ++idx;
      }
      irept copy = params;
      // Erase the parameter NAMES first: the declaration may leave a
      // parameter unnamed where the definition names it (`swap(_Tp&,
      // _Tp&)` vs `swap(_Tp& __a, _Tp& __b)`, libstdc++ bits/move.h) --
      // only the TYPES are signature ([dcl.fct]/5).
      for(auto &pdecl : copy.get_sub())
      {
        if(pdecl.id() != ID_cpp_declaration)
          continue;
        for(auto &d : static_cast<cpp_declarationt &>(pdecl).declarators())
          d.name() = cpp_namet{};
      }
      std::function<void(irept &)> walk = [&](irept &n)
      {
        if(n.id() == ID_name)
        {
          const auto it = rename.find(id2string(n.get(ID_identifier)));
          if(it != rename.end())
            n.set(ID_identifier, it->second);
        }
        for(auto &sub : n.get_sub())
          walk(sub);
        for(auto &ns : n.get_named_sub())
          walk(ns.second);
      };
      walk(copy);
      return cpp_type2name(static_cast<const typet &>(copy));
    };
    if(
      normalized(f_params, forward.template_type()) !=
      normalized(c_params, candidate.template_type()))
      return false;

    // N5008 [defns.signature.templ]: a function TEMPLATE's signature
    // also includes the RETURN type; and for member functions the
    // cv-qualifiers distinguish overloads (std::_Any_data's const and
    // non-const `_M_access<_Tp>()` differ ONLY there -- unifying them
    // broke std::function's manager chain).  Compare both, with the
    // same positional normalization for the return type.
    const irept &f_ret = f_type.find(ID_return_type);
    const irept &c_ret = c_type.find(ID_return_type);
    if(
      normalized(f_ret, forward.template_type()) !=
      normalized(c_ret, candidate.template_type()))
      return false;
    if(
      forward.declarators().front().method_qualifier() !=
      candidate.declarators().front().method_qualifier())
      return false;
  }
  return true;
}

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

  if(instantiation_stack.size() == MAX_DEPTH)
  {
    show_instantiation_stack(error());
    error().source_location = source_location;
    error() << "reached maximum template recursion depth (" << MAX_DEPTH << ")"
            << eom;
    throw 0;
  }

  instantiation_levelt i_level(instantiation_stack, had_template_instantiation);
  instantiation_stack.back().source_location = source_location;
  instantiation_stack.back().identifier = template_symbol.name;
  instantiation_stack.back().full_template_args = full_template_args;

  // [temp.inst]: instantiating a template is not itself a constant
  // evaluation.  Suspend any enclosing constant-expression context so
  // the instantiated declarations/definitions (e.g. constructor SFINAE
  // constraints) are not eagerly folded; constant-required
  // sub-expressions re-establish the context via their own guards.
  non_constant_expression_contextt non_constant_guard{*this};

#ifdef DEBUG
  std::cout << "L: " << source_location << '\n';
  std::cout << "I: " << template_symbol.name << '\n';
#endif

  cpp_saved_template_mapt saved_map(template_map);

  bool specialization_given = specialization.is_not_nil();

  // If specialization arguments still contain unassigned template
  // parameters, this is a substitution failure during template
  // instantiation (per [temp.deduct]).  Throw silently so that
  // SFINAE and overload resolution can try other candidates
  // instead of reporting a hard error.
  if(specialization_template_args.has_unassigned())
    throw 0;
  DATA_INVARIANT(
    !full_template_args.has_unassigned(), "should never get 'unassigned' here");

#ifdef DEBUG
  std::cout << "A: <";
  forall_expr(it, specialization_template_args.arguments())
  {
    if(it != specialization_template_args.arguments().begin())
      std::cout << ", ";
    if(it->id() == ID_type)
      std::cout << to_string(it->type());
    else
      std::cout << to_string(*it);
  }
  std::cout << ">\n\n";
#endif

  // do we have arguments?
  if(full_template_args.arguments().empty())
  {
    // Empty args are valid for:
    // 1. Variadic templates with zero arguments (e.g., tuple<>)
    // 2. Explicit specializations with zero parameters
    const template_typet &template_type =
      to_cpp_declaration(template_symbol.type).template_type();
    const auto &params = template_type.template_parameters();
    bool valid_empty = params.empty();
    if(!valid_empty)
    {
      valid_empty = true;
      for(const auto &p : params)
      {
        if(!p.get_bool(ID_ellipsis))
        {
          valid_empty = false;
          break;
        }
      }
    }
    if(!valid_empty)
    {
      error().source_location = source_location;
      error() << "'" << template_symbol.base_name
              << "' is a template; thus, expected template arguments" << eom;
      throw 0;
    }
  }

  // produce new symbol name
  std::string suffix = template_suffix(full_template_args);

  // N5008 [temp.deduct.type]/8: a deduced template-template-parameter
  // binding (the argument INSTANCE) may flow here as the "template" to
  // instantiate with new arguments; derive the TEMPLATE the instance
  // was created from (see class_template_symbol for the same
  // treatment and cpp_typecheck_resolve.cpp for the deduction-side
  // convention).
  if(
    !template_symbol.type.get_bool(ID_is_template) &&
    (template_symbol.type.id() == ID_struct ||
     template_symbol.type.id() == ID_union) &&
    template_symbol.type.find(ID_full_template_args).is_not_nil())
  {
    const auto tmpl_ids = cpp_scopes.get_root_scope().lookup(
      template_symbol.base_name,
      cpp_scopet::RECURSIVE,
      cpp_idt::id_classt::TEMPLATE);
    for(const auto *tid : tmpl_ids)
    {
      const symbolt *cand = symbol_table.lookup(tid->identifier);
      if(
        cand != nullptr && cand->type.get_bool(ID_is_template) &&
        to_cpp_declaration(cand->type).type().get(ID_specialization_of).empty())
      {
        return instantiate_template(
          source_location,
          *cand,
          specialization_template_args,
          full_template_args,
          specialization);
      }
    }
  }

  // we need the template scope to see the template parameters
  cpp_scopet *template_scope = id_map_lookup(cpp_scopes, template_symbol.name);

  if(template_scope == nullptr)
  {
    error().source_location = source_location;
    error() << "template scope '" << template_symbol.base_name << "' not found"
            << eom;
    throw 0;
  }

  // [temp.point] p1: When a function template is instantiated, the
  // definition (not just a forward declaration) must be used.  If the
  // template_symbol is a forward declaration (no body), search the
  // parent scope for the definition of the same template.
  const symbolt *effective_template = &template_symbol;
  {
    const cpp_declarationt &check_decl =
      to_cpp_declaration(template_symbol.type);
    if(
      !check_decl.declarators().empty() &&
      check_decl.declarators()[0].value().is_nil())
    {
      cpp_scopet &parent = template_scope->get_parent();
      cpp_scopet::id_sett id_set =
        parent.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);
      for(const auto *id_ptr : id_set)
      {
        if(id_ptr->identifier == template_symbol.name)
          continue;
        const symbolt *candidate = symbol_table.lookup(id_ptr->identifier);
        if(
          candidate != nullptr && candidate->type.get_bool(ID_is_template) &&
          candidate->base_name == template_symbol.base_name)
        {
          const cpp_declarationt &cand_decl =
            to_cpp_declaration(candidate->type);
          if(
            !cand_decl.declarators().empty() &&
            cand_decl.declarators()[0].value().is_not_nil() &&
            function_template_signatures_equivalent(check_decl, cand_decl))
          {
            effective_template = candidate;
            template_scope = id_map_lookup(cpp_scopes, candidate->name);
            break;
          }
        }
      }
    }
  }

  // produce new declaration
  cpp_declarationt new_decl = to_cpp_declaration(effective_template->type);

  // The new one is not a template any longer, but we remember the
  // template type that was used.
  template_typet template_type = new_decl.template_type();
  new_decl.remove(ID_is_template);
  new_decl.remove(ID_template_type);
  new_decl.set(ID_C_template, template_symbol.name);
  new_decl.set(ID_C_template_arguments, specialization_template_args);

  // save old scope
  cpp_save_scopet saved_scope(cpp_scopes);

  // mapping from template parameters to values/types
  template_map.build(template_type, specialization_template_args);

  // N5008 [temp.spec.partial.match]: a partial specialization's parameters
  // are bound by DEDUCTION from its argument pattern, not positionally from
  // the instance's template-argument list.  build() above received the FLAT
  // deduced list, which cannot encode multi-pack or non-trailing-pack splits
  // (e.g. libc++'s __make_tuple_types_flat<_Tuple<_Types...>,
  // __tuple_indices<_Idx...>>), so consumers that later need this instance's
  // parameter bindings -- a member alias template's body resolved via
  // resolve_template_alias -- would find the packs unbound and fail.
  // Re-run the pattern deduction here and persist the bindings on the
  // instance symbol (#spec_template_packs, mirroring #fn_template_packs for
  // member function templates).
  irept spec_bindings;
  {
    const auto &pattern_args =
      to_cpp_declaration(template_symbol.type).partial_specialization_args();
    // N5008 [temp.spec.partial.match]/2: the specialization's argument
    // pattern is matched against the actual arguments, a TRAILING pack
    // pattern matching the (possibly empty) remainder --
    // `__tuple_impl<__tuple_indices<_Indx...>, _Tp...>` matches
    // `__tuple_impl<__tuple_indices<0>>` with _Tp = {} ([temp.variadic]).
    // Requiring equal counts skipped the deduction entirely for empty
    // trailing packs, so the LEADING pack (_Indx, deduced from the
    // nested pattern) was never recorded and a base-specifier pack over
    // it (`__tuple_leaf<_Indx>...`) expanded to nothing.
    const bool trailing_pack_pattern =
      !pattern_args.arguments().empty() &&
      (pattern_args.arguments().back().get_bool(ID_ellipsis) ||
       pattern_args.arguments().back().find(ID_type).get_bool(ID_ellipsis));
    std::size_t sb_n_packs = 0;
    for(const auto &tp : template_type.template_parameters())
      if(tp.get_bool(ID_ellipsis))
        ++sb_n_packs;
    if(
      !pattern_args.arguments().empty() &&
      (pattern_args.arguments().size() ==
         full_template_args.arguments().size() ||
       (trailing_pack_pattern && pattern_args.arguments().size() ==
                                   full_template_args.arguments().size() + 1) ||
       (trailing_pack_pattern && sb_n_packs >= 2 &&
        pattern_args.arguments().size() <
          full_template_args.arguments().size())))
    {
      cpp_saved_template_mapt saved_map_for_deduction(template_map);
      cpp_save_scopet save_scope_for_deduction(cpp_scopes);
      template_map.build_unassigned(template_type);
      // Pattern names resolve in the specialization's own scope (the
      // selection loop in this function does the same before guessing).
      cpp_scopet *spec_scope = id_map_lookup(cpp_scopes, template_symbol.name);
      if(spec_scope != nullptr)
        cpp_scopes.go_to(*spec_scope);
      cpp_typecheck_resolvet resolver(*this);
      // [temp.deduct.type]/8: partial-specialization matching
      // rejects cv-mismatched patterns (see the flag's doc in
      // cpp_typecheck_resolve.h).
      resolver.strict_cv_deduction = true;
      try
      {
        const std::size_t sb_npat = pattern_args.arguments().size();
        const std::size_t sb_nfull = full_template_args.arguments().size();
        const bool sb_absorb =
          trailing_pack_pattern && sb_n_packs >= 2 && sb_npat <= sb_nfull;
        const std::size_t sb_pos =
          sb_absorb ? sb_npat - 1 : std::min(sb_npat, sb_nfull);
        for(std::size_t i = 0; i < sb_pos; ++i)
        {
          if(full_template_args.arguments()[i].id() == ID_type)
            resolver.guess_template_args(
              pattern_args.arguments()[i].type(),
              full_template_args.arguments()[i].type());
          else
            resolver.guess_template_args(
              pattern_args.arguments()[i], full_template_args.arguments()[i]);
        }
        if(!sb_absorb)
        {
          for(std::size_t i = sb_pos; i < sb_nfull && i < sb_npat; ++i)
          {
            if(full_template_args.arguments()[i].id() == ID_type)
              resolver.guess_template_args(
                pattern_args.arguments()[i].type(),
                full_template_args.arguments()[i].type());
            else
              resolver.guess_template_args(
                pattern_args.arguments()[i], full_template_args.arguments()[i]);
          }
        }
        else
        {
          // N5008 [temp.spec.partial.match]/2: bind the remainder as
          // ONE pack (see the selection loop; __tuple_impl's
          // <long... _Indx, class... _Tp> head instantiated directly
          // with flat args needs _Tp = {int, int}, or the
          // __tuple_leaf<_Indx> bases are never created and get's
          // derived-to-base static_cast silently drops its body).
          const auto &last = pattern_args.arguments().back();
          const irept &last_t =
            last.id() == ID_ambiguous || last.id() == ID_type
              ? static_cast<const irept &>(last.type())
              : static_cast<const irept &>(last);
          irep_idt pack_id;
          if(
            last_t.id() == ID_cpp_name && !last_t.get_sub().empty() &&
            last_t.get_sub().front().id() == ID_name)
          {
            const irep_idt pn = last_t.get_sub().front().get(ID_identifier);
            const auto ids = cpp_scopes.current_scope().lookup(
              pn,
              cpp_scopet::RECURSIVE,
              cpp_idt::id_classt::TEMPLATE_PARAMETER);
            for(const auto *idp : ids)
              pack_id = idp->identifier;
          }
          if(!pack_id.empty())
          {
            std::vector<typet> pack_elems;
            std::vector<exprt> pack_exprs;
            for(std::size_t j = sb_pos; j < sb_nfull; ++j)
            {
              const auto &a = full_template_args.arguments()[j];
              if(a.id() == ID_type)
              {
                if(a.type().id() != ID_empty)
                  pack_elems.push_back(a.type());
              }
              else if(a.id() != ID_unassigned)
                pack_exprs.push_back(a);
            }
            template_map.pack_size_map[pack_id] =
              pack_elems.size() + pack_exprs.size();
            // Single-element-only scalar entries; see the matching
            // comment in the selection loop above.
            if(!pack_exprs.empty())
            {
              template_map.pack_expr_map[pack_id] = pack_exprs;
              if(pack_exprs.size() == 1)
                template_map.expr_map[pack_id] = pack_exprs.front();
            }
            else
            {
              template_map.pack_args_map[pack_id] = pack_elems;
              if(pack_elems.size() == 1)
                template_map.type_map[pack_id] = pack_elems.front();
            }
          }
        }
        // an unmatched trailing pack pattern deduces the EMPTY pack
        // ([temp.variadic]/7)
        if(
          pattern_args.arguments().size() ==
          full_template_args.arguments().size() + 1)
        {
          const auto &last_param = template_type.template_parameters().back();
          if(last_param.get_bool(ID_ellipsis))
          {
            const irep_idt pid = last_param.id() == ID_type
                                   ? last_param.type().get(ID_identifier)
                                   : last_param.get(ID_identifier);
            if(!pid.empty())
              template_map.pack_size_map[pid] = 0;
          }
        }
      }
      catch(...)
      {
        // deduction failure here is non-fatal: we simply persist nothing
      }
      for(const auto &param : template_type.template_parameters())
      {
        const irep_idt pid = param.id() == ID_type
                               ? param.type().get(ID_identifier)
                               : param.get(ID_identifier);
        if(pid.empty())
          continue;
        const bool param_is_pack = param.get_bool(ID_ellipsis);
        auto pack_t = template_map.pack_args_map.find(pid);
        if(pack_t != template_map.pack_args_map.end())
        {
          irept entry{"pack_types"};
          entry.set(ID_identifier, pid);
          for(const auto &t : pack_t->second)
            entry.get_sub().push_back(t);
          spec_bindings.get_sub().push_back(std::move(entry));
          continue;
        }
        auto pack_e = template_map.pack_expr_map.find(pid);
        if(pack_e != template_map.pack_expr_map.end())
        {
          irept entry{"pack_exprs"};
          entry.set(ID_identifier, pid);
          for(const auto &e : pack_e->second)
            entry.get_sub().push_back(e);
          spec_bindings.get_sub().push_back(std::move(entry));
          continue;
        }
        auto st = template_map.type_map.find(pid);
        if(
          st != template_map.type_map.end() && st->second.id() != ID_unassigned)
        {
          irept entry{param_is_pack ? "pack_types" : "scalar_type"};
          entry.set(ID_identifier, pid);
          entry.get_sub().push_back(st->second);
          spec_bindings.get_sub().push_back(std::move(entry));
          continue;
        }
        auto se = template_map.expr_map.find(pid);
        if(
          se != template_map.expr_map.end() && se->second.id() != ID_unassigned)
        {
          irept entry{param_is_pack ? "pack_exprs" : "scalar_expr"};
          entry.set(ID_identifier, pid);
          entry.get_sub().push_back(se->second);
          spec_bindings.get_sub().push_back(std::move(entry));
          continue;
        }
        // A pack deduced EMPTY has no element entry at all, only a
        // zero in pack_size_map ([temp.variadic]/7) -- record it, or
        // sizeof...(EmptyPack) in a member initializer is unresolvable.
        auto ps = template_map.pack_size_map.find(pid);
        if(
          param_is_pack && ps != template_map.pack_size_map.end() &&
          ps->second == 0)
        {
          irept entry{"pack_empty"};
          entry.set(ID_identifier, pid);
          spec_bindings.get_sub().push_back(std::move(entry));
        }
      }
    }
  }

  // N5008 [temp.inst]/2 + [temp.spec.partial]: the members of the
  // instantiated partial specialization are typechecked with the
  // specialization's OWN parameters bound to their DEDUCED values.
  // The deduction above ran under a saved-map guard (so the guessing
  // could not leak), recording into spec_bindings for later alias
  // resolution -- but the class-body conversion below ALSO needs the
  // pack bindings: without them `sizeof...(_Idx)` in a static data
  // member's initializer (libc++ __perfect_forward_impl) resolves
  // against an empty pack_size_map, the SFINAE guard swallows the
  // failure, and the RAW initializer reaches goto conversion (symex
  // then crashes on the malformed assignment).  Replay the bindings
  // into the active map.
  for(const auto &entry : spec_bindings.get_sub())
  {
    const irep_idt pid = entry.get(ID_identifier);
    if(entry.id() == "pack_types")
    {
      std::vector<typet> elems;
      for(const auto &t : entry.get_sub())
        elems.push_back(static_cast<const typet &>(t));
      template_map.pack_size_map[pid] = elems.size();
      template_map.pack_args_map[pid] = elems;
      if(!elems.empty())
        template_map.type_map[pid] = elems.front();
    }
    else if(entry.id() == "pack_exprs")
    {
      std::vector<exprt> vals;
      for(const auto &e : entry.get_sub())
        vals.push_back(static_cast<const exprt &>(e));
      template_map.pack_size_map[pid] = vals.size();
      template_map.pack_expr_map[pid] = vals;
      if(!vals.empty())
        template_map.expr_map[pid] = vals.front();
    }
    else if(entry.id() == "pack_empty")
    {
      template_map.pack_size_map[pid] = 0;
    }
    else if(entry.id() == "scalar_type" && !entry.get_sub().empty())
    {
      template_map.type_map[pid] =
        static_cast<const typet &>(entry.get_sub().front());
    }
    else if(entry.id() == "scalar_expr" && !entry.get_sub().empty())
    {
      template_map.expr_map[pid] =
        static_cast<const exprt &>(entry.get_sub().front());
    }
  }

  // N5008 [temp.variadic]/5: when the template ends in a parameter pack, bind
  // that pack to its full deduced element sequence taken from
  // full_template_args.  build() above is driven by
  // specialization_template_args, which for a trailing-pack partial
  // specialization carries the pack collapsed to a single scalar element
  // (build_template_args emits one argument per parameter); left uncorrected
  // that makes a base-specifier or member pack expansion `Pack...` in the
  // instantiated body expand to the first element only (e.g. a recursive base
  // `Rec<I+1, T...>` would instantiate `Rec<1, int>` instead of
  // `Rec<1, int, int>`).  The partial specialization's argument pattern is
  // positionally aligned with full_template_args (its leading parameters map
  // to the leading arguments and the trailing pack to the rest), so recover
  // the full pack from the trailing arguments.  Only act when this yields more
  // elements than build() recorded, so single-element and empty packs -- and
  // the established free-function expander below -- are undisturbed.
  //
  // Restricted to partial-specialization instantiations: only there does
  // specialization_template_args arrive from build_template_args with the pack
  // collapsed.  A primary template is instantiated directly from its full
  // argument list, so build() already binds its pack correctly and this
  // correction must not perturb it.
  //
  // When the identity trailing-pack shape is detected, the instance's recorded
  // template arguments (ID_C_template_arguments) must likewise be the full,
  // expanded list rather than the pack-collapsed specialization_template_args,
  // so that argument-deduction *against this instance* (e.g. libstdc++'s
  // `std::get`/`__get_helper` deducing `_Head, _Tail...` from a `_Tuple_impl`
  // argument) sees the whole pack.
  bool record_full_template_args = false;
  if(
    !template_symbol.type.get(ID_specialization_of).empty() &&
    !template_type.template_parameters().empty())
  {
    const auto &last_param = template_type.template_parameters().back();
    // Positional recovery from full_template_args is only valid when the
    // specialization's written argument list is the *identity* pattern
    // `<p0, p1, ..., pk, Pack...>` -- each leading argument a bare parameter
    // name and the last a bare pack -- so that argument j corresponds to the
    // j-th template parameter.  A specialization with a constructed or nested
    // pattern (e.g. `tuple_size<tuple<T...>>`, where the pack is nested inside
    // a template-id) is NOT positionally aligned; recovering a pack from the
    // top-level arguments there would bind the wrong types and trigger runaway
    // instantiation.  Detect the identity shape and bail out otherwise.
    bool identity_trailing_pack = last_param.get_bool(ID_ellipsis);
    if(identity_trailing_pack)
    {
      const cpp_declarationt &decl = to_cpp_declaration(template_symbol.type);
      const auto &psa = decl.partial_specialization_args().arguments();
      const auto &params = template_type.template_parameters();
      if(psa.size() != params.size())
        identity_trailing_pack = false;
      for(std::size_t k = 0; identity_trailing_pack && k < psa.size(); ++k)
      {
        const irept *a = &static_cast<const irept &>(psa[k]);
        if(a->id() == ID_ambiguous || a->id() == ID_type)
          a = &a->find(ID_type);
        // A bare parameter reference is a cpp_name with no template-argument
        // list.
        if(a->id() != ID_cpp_name)
          identity_trailing_pack = false;
        else
          for(const auto &sub : a->get_sub())
            if(sub.id() == ID_template_args)
            {
              identity_trailing_pack = false;
              break;
            }
      }
    }
    if(identity_trailing_pack)
    {
      // The full argument list is positionally aligned with this
      // specialization's parameters; record it (below) instead of the
      // pack-collapsed specialization_template_args.
      record_full_template_args = true;
      const irep_idt pack_id = last_param.id() == ID_type
                                 ? last_param.type().get(ID_identifier)
                                 : last_param.get(ID_identifier);
      const std::size_t non_pack =
        template_type.template_parameters().size() - 1;
      if(!pack_id.empty() && full_template_args.arguments().size() >= non_pack)
      {
        std::vector<typet> pack_elems;
        for(std::size_t j = non_pack; j < full_template_args.arguments().size();
            ++j)
        {
          const auto &a = full_template_args.arguments()[j];
          if(a.id() == ID_type && a.type().id() != ID_empty)
            pack_elems.push_back(a.type());
        }
        auto pa_it = template_map.pack_args_map.find(pack_id);
        const std::size_t have =
          pa_it == template_map.pack_args_map.end() ? 0 : pa_it->second.size();
        if(pack_elems.size() > have)
        {
          template_map.pack_args_map[pack_id] = pack_elems;
          template_map.pack_size_map[pack_id] = pack_elems.size();
          // A parameter pack may only appear in a pack-expansion context, so
          // it must not retain a scalar type_map binding: build() recorded the
          // pack's single collapsed element as type_map[pack_id], which would
          // shadow the pack and make a base-specifier / member expansion
          // `pack...` resolve to that one element.  Erase it so the expansion
          // is driven by pack_args_map and yields all elements.
          template_map.type_map.erase(pack_id);
        }
      }
    }
  }

  // Per [temp.variadic]/7: for constructor templates with variadic packs,
  // remove empty pack parameters and substitute non-empty pack names.
  if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
  {
    bool has_variadic = false;
    for(const auto &p : template_type.template_parameters())
      if(p.get_bool(ID_ellipsis))
        has_variadic = true;
    // Apply pack removal to all function templates with variadic packs
    // per [temp.variadic]/7.
    if(!has_variadic)
      goto skip_pack_removal;

    // Only collect empty pack names from THIS template's parameters
    std::set<std::string> ep_names;
    for(const auto &tp : template_type.template_parameters())
    {
      if(!tp.get_bool(ID_ellipsis))
        continue;
      irep_idt pid = tp.type().get(ID_identifier);
      if(pid.empty())
        continue;
      auto it = template_map.pack_size_map.find(pid);
      if(it != template_map.pack_size_map.end() && it->second == 0)
      {
        const std::string f = id2string(pid);
        auto p = f.rfind("::");
        ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
    }
    if(!ep_names.empty())
    {
      std::function<bool(const irept &)> refs_ep = [&](const irept &n) -> bool
      {
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &s : n.get_sub())
          if(refs_ep(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(refs_ep(ns.second))
            return true;
        return false;
      };
      auto &decl = new_decl.declarators()[0];
      if(decl.type().id() == ID_function_type)
      {
        irept &params = decl.type().add(ID_parameters);
        params.get_sub().erase(
          std::remove_if(
            params.get_sub().begin(),
            params.get_sub().end(),
            [&](const irept &p)
            {
              if(p.id() != ID_cpp_declaration)
                return false;
              // N5008 [temp.variadic]/7: only a *function parameter pack*
              // -- a parameter declared with a top-level `...`, e.g.
              // `_T... args` -- expands to an empty parameter list when the
              // pack is empty and is therefore removed.  A parameter whose
              // type merely *contains* the empty pack nested inside a
              // template-argument pack expansion (e.g. `Base<_H, _T...>
              // &__b`, or `tuple<_T...> t`) is a single parameter: the empty
              // expansion collapses the argument list (to `Base<_H>` /
              // `tuple<>`) but the parameter itself must be kept.  Removing
              // it leaves the instantiated function with no parameter and an
              // unbindable call (see
              // regression/cbmc-cpp/cpp11_derived_to_base_pack_call_in_body).
              // Detect a genuine parameter pack by the top-level ellipsis on
              // the declarator/type only; do NOT remove on a mere nested
              // occurrence of the pack name.
              //
              // And only remove it when ITS OWN pack is among the empty
              // ones: with MULTIPLE template parameter packs (libc++
              // __tuple_impl's five-pack constructor, `_Ul`/`_Tl` empty
              // but `_Up` two-element), removing every ellipsis parameter
              // dropped the NON-empty `_Up&&... __u` too, leaving a
              // 4-parameter constructor no 6-argument call can match
              // ([temp.variadic]/7 applies per pack, not per overload).
              for(const auto &d : p.get_sub())
              {
                if(
                  d.id() != ID_cpp_declarator ||
                  (!d.find(ID_type).get_bool(ID_ellipsis) &&
                   !d.get_bool(ID_ellipsis)))
                  continue;
                const auto &pd = static_cast<const cpp_declarationt &>(p);
                const irept *t = &static_cast<const irept &>(pd.type());
                while(t->id() != ID_cpp_name && !t->get_sub().empty())
                  t = &t->get_sub().front();
                std::string own;
                if(t->id() == ID_cpp_name && !t->get_sub().empty())
                  own = id2string(t->get_sub().front().get(ID_identifier));
                return own.empty() || ep_names.count(own) != 0;
              }
              return false;
            }),
          params.get_sub().end());
      }
      irept &mi = decl.add(ID_member_initializers);
      // A reference to the (empty) pack anywhere in an initializer argument
      // marks it as a pack expansion to be dropped ([temp.variadic]/4: a
      // pack can only appear expanded; the parser may lose the `...`) --
      // EXCEPT under `sizeof...`, which is a complete expression whose
      // value for an empty pack is simply 0 ([temp.variadic]/8), e.g.
      // `typename _Build_index_tuple<sizeof...(_Args2)>::__type()` in
      // std::pair's delegating piecewise constructor: that argument must
      // be KEPT, or the delegation call's arguments shift and the target
      // constructor no longer resolves.
      std::function<bool(const irept &)> refs_ep_outside_sizeof =
        [&](const irept &n) -> bool
      {
        if(n.get_bool("#sizeof_pack"))
          return false;
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &sn : n.get_sub())
          if(refs_ep_outside_sizeof(sn))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(refs_ep_outside_sizeof(ns.second))
            return true;
        return false;
      };
      for(auto &init : mi.get_sub())
      {
        auto &subs = init.get_sub();
        subs.erase(
          std::remove_if(
            subs.begin(),
            subs.end(),
            [&](const irept &s) { return refs_ep_outside_sizeof(s); }),
          subs.end());
      }
    }
    // Per [temp.variadic]/7: for non-empty packs, substitute
    // pack parameter names with actual type base names and
    // remove ellipsis from expanded expressions.
    if(!template_map.pack_args_map.empty())
    {
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        // N5008 [temp.variadic]/5: only a SINGLE-element pack may have its
        // name textually replaced by "the" element -- for that arity the
        // front element IS the k-th element of every expansion.  A pack
        // with >= 2 elements referenced inside a not-yet-expanded pack
        // expansion pattern (e.g. the mem-init argument
        // `forward_<Args>(a)...` of libstdc++ _Hashtable's _Scoped_node
        // constructor) must keep the pack NAME: the deferred
        // per-element expansion substitutes the k-th element in
        // lockstep.  Stamping the front element here concretized the
        // pattern to element 0 for every k, the per-element call became
        // unresolvable, and the constructor body was silently dropped
        // (the emplaced node stayed uninitialized -- the
        // unordered_map::emplace duplicate-insert wrong-code shape).
        // N5008 [temp.variadic]/5: single-element packs only -- see the
        // guarded mem-init substitution above for why a >=2-element pack
        // must keep its name (front-element stamping concretizes every
        // expansion copy to element 0).
        if(pa.second.size() != 1)
          continue;
        const std::string full = id2string(pa.first);
        auto p = full.rfind("::");
        const std::string sn =
          p != std::string::npos ? full.substr(p + 2) : full;
        const typet &t = pa.second.front();
        if(t.id() == ID_struct_tag)
        {
          // Use the full struct_tag identifier (including namespace
          // prefix and `tag-` markers).  resolve_scope can find this
          // directly via id_map.  Stripping the namespace with naive
          // string operations breaks for nested template types like
          // `std::__cxx11::tag-basic_string<char,std::tag-allocator<char>>`
          // because the `::` and `tag-` substrings inside template
          // arguments confuse the parsing.
          pack_subst[sn] = to_struct_tag_type(t).get_identifier();
        }
      }
      if(!pack_subst.empty() && !new_decl.declarators().empty())
      {
        std::function<bool(const irept &)> contains_pack =
          [&](const irept &node) -> bool
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
            return true;
          for(const auto &s : node.get_sub())
            if(contains_pack(s))
              return true;
          for(const auto &ns : node.get_named_sub())
            if(contains_pack(ns.second))
              return true;
          return false;
        };
        std::function<void(irept &)> subst = [&](irept &node)
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
          {
            node.set(
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          }
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
        subst(mi);
        // Remove ellipsis only from pack-expanded parameters
        auto &dt = new_decl.declarators()[0].type();
        if(dt.id() == ID_function_type)
        {
          irept &params = dt.add(ID_parameters);
          for(auto &p : params.get_sub())
          {
            if(contains_pack(p))
            {
              subst(p);
              p.remove(ID_ellipsis);
              for(auto &d : p.get_sub())
                d.remove(ID_ellipsis);
            }
          }
        }
      }
    }
  }
skip_pack_removal:

  // Per [temp.variadic]/7: when a variadic pack is empty, remove
  // pack-expanded parameters from the function type and remove
  // member initializer expressions referencing the empty pack.
  // This must happen immediately after build() sets pack_size_map,
  // before any code that might try to resolve the pack parameter.
  if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
  {
    // Only apply for constructor templates with variadic packs
    bool has_variadic = false;
    for(const auto &p : template_type.template_parameters())
      if(p.get_bool(ID_ellipsis))
        has_variadic = true;
    bool is_ctor = new_decl.is_constructor();
    if(!has_variadic || !is_ctor)
      goto skip_pack_removal_ft;

    // Only collect empty pack names from THIS template's parameters
    std::set<std::string> ep_names;
    for(const auto &tp : template_type.template_parameters())
    {
      if(!tp.get_bool(ID_ellipsis))
        continue;
      irep_idt pid = tp.type().get(ID_identifier);
      if(pid.empty())
        continue;
      auto it = template_map.pack_size_map.find(pid);
      if(it != template_map.pack_size_map.end() && it->second == 0)
      {
        const std::string f = id2string(pid);
        auto p = f.rfind("::");
        ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
    }
    if(!ep_names.empty())
    {
      std::function<bool(const irept &)> refs_ep = [&](const irept &n) -> bool
      {
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &s : n.get_sub())
          if(refs_ep(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(refs_ep(ns.second))
            return true;
        return false;
      };
      auto &decl = new_decl.declarators()[0];
      // Remove pack params from function type
      if(decl.type().id() == ID_function_type)
      {
        irept &params = decl.type().add(ID_parameters);
        params.get_sub().erase(
          std::remove_if(
            params.get_sub().begin(),
            params.get_sub().end(),
            [&](const irept &p)
            {
              if(p.id() != ID_cpp_declaration)
                return false;
              // N5008 [temp.variadic]/7: remove only a genuine *function
              // parameter pack* (top-level `...`); keep a parameter whose
              // type merely contains a nested empty pack expansion (its
              // argument list collapses but the parameter remains).  And
              // only when ITS OWN pack is among the empty ones -- see the
              // matching predicate earlier in instantiate_template
              // (multi-pack constructors keep their non-empty packs).
              for(const auto &d : p.get_sub())
              {
                if(
                  d.id() != ID_cpp_declarator ||
                  (!d.find(ID_type).get_bool(ID_ellipsis) &&
                   !d.get_bool(ID_ellipsis)))
                  continue;
                const auto &pd = static_cast<const cpp_declarationt &>(p);
                const irept *t = &static_cast<const irept &>(pd.type());
                while(t->id() != ID_cpp_name && !t->get_sub().empty())
                  t = &t->get_sub().front();
                std::string own;
                if(t->id() == ID_cpp_name && !t->get_sub().empty())
                  own = id2string(t->get_sub().front().get(ID_identifier));
                return own.empty() || ep_names.count(own) != 0;
              }
              return false;
            }),
          params.get_sub().end());
      }
      // Remove empty pack expressions from member initializers
      irept &mi = decl.add(ID_member_initializers);
      // A reference to the (empty) pack anywhere in an initializer argument
      // marks it as a pack expansion to be dropped ([temp.variadic]/4: a
      // pack can only appear expanded; the parser may lose the `...`) --
      // EXCEPT under `sizeof...`, which is a complete expression whose
      // value for an empty pack is simply 0 ([temp.variadic]/8), e.g.
      // `typename _Build_index_tuple<sizeof...(_Args2)>::__type()` in
      // std::pair's delegating piecewise constructor: that argument must
      // be KEPT, or the delegation call's arguments shift and the target
      // constructor no longer resolves.
      std::function<bool(const irept &)> refs_ep_outside_sizeof =
        [&](const irept &n) -> bool
      {
        if(n.get_bool("#sizeof_pack"))
          return false;
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &sn : n.get_sub())
          if(refs_ep_outside_sizeof(sn))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(refs_ep_outside_sizeof(ns.second))
            return true;
        return false;
      };
      for(auto &init : mi.get_sub())
      {
        auto &subs = init.get_sub();
        subs.erase(
          std::remove_if(
            subs.begin(),
            subs.end(),
            [&](const irept &s) { return refs_ep_outside_sizeof(s); }),
          subs.end());
      }
    }
    // Per [temp.variadic]/7: for non-empty packs, substitute
    // the pack parameter name in template_args with the actual
    // type from pack_args_map.
    if(!template_map.pack_args_map.empty())
    {
      // Build substitution map: short_name → type identifier
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        // N5008 [temp.variadic]/5: single-element packs only -- see the
        // guarded mem-init substitution above for why a >=2-element pack
        // must keep its name (front-element stamping concretizes every
        // expansion copy to element 0).
        if(pa.second.size() != 1)
          continue;
        const std::string full = id2string(pa.first);
        auto p = full.rfind("::");
        const std::string sn =
          p != std::string::npos ? full.substr(p + 2) : full;
        // For single-element packs, get the type's name
        const typet &t = pa.second.front();
        if(t.id() == ID_struct_tag)
        {
          std::string tag = id2string(to_struct_tag_type(t).get_identifier());
          if(tag.substr(0, 4) == "tag-")
            tag = tag.substr(4);
          pack_subst[sn] = tag;
        }
      }
      if(!pack_subst.empty() && !new_decl.declarators().empty())
      {
        // Substitute in member initializers
        std::function<void(irept &)> subst = [&](irept &node)
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
          {
            node.set(
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          }
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
        subst(mi);
      }
    }
  }
skip_pack_removal_ft:

  // enter the template scope
  cpp_scopes.go_to(*template_scope);

  // For nested member class templates (e.g., Outer<int>::Inner<double>),
  // the outer template parameters (T) need to be in the template map
  // so that references to T in Inner's body can be resolved.
  if(new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
  {
    cpp_scopet *scope = &template_scope->get_parent();
    while(scope != nullptr && !scope->is_root_scope())
    {
      if(scope->is_class())
      {
        const auto *class_sym = symbol_table.lookup(scope->identifier);
        if(
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template).is_not_nil() &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil())
        {
          template_map.build(
            static_cast<const template_typet &>(
              class_sym->type.find(ID_C_template)),
            static_cast<const cpp_template_args_tct &>(
              class_sym->type.find(ID_C_template_arguments)));
        }
      }
      scope = &scope->get_parent();
    }
  }

  // Is it a template method?
  // It's in the scope of a class, and not a class itself.
  bool is_template_method =
    cpp_scopes.current_scope().get_parent().is_class() &&
    new_decl.type().id() != ID_struct && new_decl.type().id() != ID_union;

  irep_idt class_name;

  if(is_template_method)
    class_name = cpp_scopes.current_scope().get_parent().identifier;

  // sub-scope for fixing the prefix
  cpp_scopet &sub_scope = sub_scope_for_instantiation(*template_scope, suffix);

  // let's see if we have the instance already
  {
    cpp_scopet::id_sett id_set =
      sub_scope.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

    if(id_set.size() == 1)
    {
      // It has already been instantiated!
      const cpp_idt &cpp_id = **id_set.begin();

      DATA_INVARIANT(
        cpp_id.id_class == cpp_idt::id_classt::CLASS ||
          cpp_id.id_class == cpp_idt::id_classt::TYPEDEF ||
          cpp_id.id_class == cpp_idt::id_classt::SYMBOL,
        "id must be class, typedef, or symbol");

      const symbolt &symb = lookup(cpp_id.identifier);

      // continue if the type is incomplete only
      if(
        cpp_id.id_class == cpp_idt::id_classt::CLASS &&
        (symb.type.id() == ID_struct || symb.type.id() == ID_union))
      {
        // ... unless a base-specifier was dropped because its type was
        // still incomplete at the previous (eager) point of
        // instantiation AND that type has meanwhile been completed; the
        // present use is a new point of instantiation ([temp.point])
        // and must rebuild the layout.  While the base's type is STILL
        // incomplete, rebuilding is pointless (and looped to the
        // recursion limit), so the degenerate instance is served as-is.
        if(!dropped_base_now_complete(symb.type))
          return symb;
      }
      else if(cpp_id.id_class == cpp_idt::id_classt::TYPEDEF)
        return symb;
      else if(symb.value.is_not_nil() && symb.type.id() == ID_code)
        return symb;
    }
    else if(
      new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
    {
      // The sub-scope lookup may fail when a template is forward-declared
      // in one scope and defined in another (creating different template
      // scopes). Check the symbol table directly for an existing
      // instantiation.
      const irep_idt identifier = id2string(sub_scope.prefix) + "tag-" +
                                  id2string(template_symbol.base_name) + suffix;
      auto s_it = symbol_table.symbols.find(identifier);
      if(
        s_it != symbol_table.symbols.end() &&
        (s_it->second.type.id() == ID_struct ||
         s_it->second.type.id() == ID_union) &&
        !to_struct_union_type(s_it->second.type).is_incomplete())
      {
        return s_it->second;
      }

      // If the symbol exists but is incomplete, the class scope was
      // created under a different (e.g., forward-declaration) template
      // scope that may lack named template parameters. Copy template
      // parameter entries from the current template scope into the
      // class scope so they are visible during elaboration.
      if(s_it != symbol_table.symbols.end())
      {
        auto class_scope_it = cpp_scopes.id_map.find(identifier);
        if(class_scope_it != cpp_scopes.id_map.end())
        {
          cpp_scopet &class_scope =
            static_cast<cpp_scopet &>(*class_scope_it->second);
          for(const auto &param : template_type.template_parameters())
          {
            irep_idt param_base_name;
            if(param.id() == ID_type)
              param_base_name = param.type().get(ID_identifier);
            else
              param_base_name = param.get(ID_identifier);
            if(param_base_name.empty())
              continue;
            const std::string pstr = id2string(param_base_name);
            auto pos = pstr.rfind("::");
            irep_idt base = pos != std::string::npos
                              ? irep_idt(pstr.substr(pos + 2))
                              : param_base_name;
            auto tp_set = template_scope->lookup(
              base,
              cpp_scopet::SCOPE_ONLY,
              cpp_idt::id_classt::TEMPLATE_PARAMETER);
            for(auto *tp : tp_set)
              class_scope.insert(*tp);
          }
        }
      }
    }

    cpp_scopes.go_to(sub_scope);
  }

  // store the information that the template has
  // been instantiated using these arguments
  {
    // need non-const handle on template symbol
    symbolt &s = symbol_table.get_writeable_ref(template_symbol.name);
    irept &instantiated_with = s.value.add(ID_instantiated_with);
    instantiated_with.get_sub().push_back(specialization_template_args);
  }

#ifdef DEBUG
  std::cout << "CLASS MAP:\n";
  template_map.print(std::cout);
#endif

  // fix the type
  {
    typet declaration_type = new_decl.type();

    // specialization?
    if(specialization_given)
    {
      if(declaration_type.id() == ID_struct)
      {
        declaration_type = specialization;
        declaration_type.add_source_location() = source_location;
      }
      else
      {
        irept tmp = specialization;
        new_decl.declarators()[0].swap(tmp);
      }
    }

    template_map.apply(declaration_type);
    new_decl.type().swap(declaration_type);

    // Also apply template_map to template parameter defaults.
    // Default arguments like "class = _Templ<_Args...>" contain
    // template parameters that need substitution.
    for(auto &param : new_decl.template_type().template_parameters())
    {
      if(param.has_default_argument())
      {
        exprt &def = static_cast<exprt &>(param.add(ID_C_default_value));
        template_map.apply(def);
        if(def.id() == ID_type)
          template_map.apply(def.type());
      }
    }

    // Expand fold expressions in the class body.
    // Fold expressions like (Bs && ...) reference pack parameters.
    // We expand them into binary expression trees using the actual
    // template arguments.
    if(
      (new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union) &&
      !template_type.template_parameters().empty() &&
      template_type.template_parameters().back().get_bool(ID_ellipsis))
    {
      const auto &pack_param = template_type.template_parameters().back();
      irep_idt pack_base_name;
      if(pack_param.id() == ID_type)
        pack_base_name = pack_param.type().get(ID_identifier);
      else
        pack_base_name = pack_param.get(ID_identifier);

      const std::string pstr = id2string(pack_base_name);
      auto pos = pstr.rfind("::");
      const std::string short_name =
        pos != std::string::npos ? pstr.substr(pos + 2) : pstr;

      const std::size_t non_pack =
        template_type.template_parameters().size() - 1;
      std::vector<exprt> pack_args;
      for(std::size_t k = non_pack; k < full_template_args.arguments().size();
          ++k)
        pack_args.push_back(full_template_args.arguments()[k]);

      auto is_pack_ref = [&short_name](const irept &n) -> bool
      {
        if(n.id() == ID_name)
          return id2string(n.get(ID_identifier)) == short_name;
        if(n.id() == ID_cpp_name && !n.get_sub().empty())
        {
          const auto &front = n.get_sub().front();
          if(front.id() == ID_name)
            return id2string(front.get(ID_identifier)) == short_name;
        }
        return false;
      };

      std::function<bool(const irept &)> contains_pack_ref;
      contains_pack_ref = [&is_pack_ref,
                           &contains_pack_ref](const irept &n) -> bool
      {
        if(is_pack_ref(n))
          return true;
        for(const auto &s : n.get_sub())
          if(contains_pack_ref(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(contains_pack_ref(ns.second))
            return true;
        return false;
      };

      std::function<irept(const irept &, const exprt &)> substitute_arg;
      substitute_arg = [&is_pack_ref, &substitute_arg, &short_name](
                         const irept &n, const exprt &arg) -> irept
      {
        // N5008 [temp.variadic]/5: substitute the pack element INTO the
        // pattern.  A QUALIFIED pack reference (`Ts::v` -- fold over a
        // member of each pack element, e.g.
        // `static inline int value = (Ts::v + ...)`) must keep its
        // trailing components: replace only the leading name component
        // with the element's struct tag identifier, which resolve_scope
        // finds directly via id_map/symbol_table (same technique as the
        // member-initializer pack substitution).  Wholesale replacement
        // would turn `Ts::v` into just the type, leaving a
        // type-inconsistent initializer that trips a symex invariant.
        if(
          n.id() == ID_cpp_name && n.get_sub().size() > 1 &&
          n.get_sub().front().id() == ID_name &&
          id2string(n.get_sub().front().get(ID_identifier)) == short_name &&
          arg.id() == ID_type && arg.type().id() == ID_struct_tag)
        {
          irept result = n;
          result.get_sub().front().set(
            ID_identifier, to_struct_tag_type(arg.type()).get_identifier());
          return result;
        }
        if(is_pack_ref(n))
          return arg;
        irept result = n;
        for(auto &s : result.get_sub())
          s = substitute_arg(s, arg);
        return result;
      };

      std::function<void(irept &)> expand_folds;
      expand_folds = [&](irept &node)
      {
        if(
          (node.id() == irep_idt("cpp_right_fold") ||
           node.id() == irep_idt("cpp_left_fold")) &&
          !node.get_sub().empty() && contains_pack_ref(node.get_sub().front()))
        {
          const irep_idt fold_op = node.get(irep_idt("fold_op"));
          const irept &pack_expr = node.get_sub().front();
          bool is_left = (node.id() == irep_idt("cpp_left_fold"));

          if(pack_args.empty())
          {
            if(fold_op == ID_and)
              node = true_exprt();
            else if(fold_op == ID_or)
              node = false_exprt();
            else
              node = from_integer(0, signed_int_type());
            return;
          }

          if(pack_args.size() == 1)
          {
            node = substitute_arg(pack_expr, pack_args[0]);
            return;
          }

          if(is_left)
          {
            irept result = substitute_arg(pack_expr, pack_args[0]);
            for(std::size_t i = 1; i < pack_args.size(); ++i)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(result);
              bin.get_sub().push_back(substitute_arg(pack_expr, pack_args[i]));
              result = bin;
            }
            node = result;
          }
          else
          {
            irept result =
              substitute_arg(pack_expr, pack_args[pack_args.size() - 1]);
            for(int i = static_cast<int>(pack_args.size()) - 2; i >= 0; --i)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(substitute_arg(pack_expr, pack_args[i]));
              bin.get_sub().push_back(result);
              result = bin;
            }
            node = result;
          }
          return;
        }

        // N5008 [expr.prim.fold]/2: binary folds.  Parser layout:
        // sub[0] = the operand left of `op ...`, sub[1] = the operand right
        // of `... op`.  `(init op ... op pack)` is a binary LEFT fold
        // (((init op e0) op e1) ...); `(pack op ... op init)` is a binary
        // RIGHT fold (e0 op (e1 op (... op init))).
        if(
          node.id() == irep_idt("cpp_binary_fold") &&
          node.get_sub().size() >= 2)
        {
          const irep_idt fold_op = node.get(irep_idt("fold_op"));
          const bool pack_on_right = contains_pack_ref(node.get_sub()[1]);
          const bool pack_on_left = contains_pack_ref(node.get_sub()[0]);
          if(pack_on_left || pack_on_right)
          {
            irept init_expr =
              pack_on_right ? node.get_sub()[0] : node.get_sub()[1];
            const irept pattern =
              pack_on_right ? node.get_sub()[1] : node.get_sub()[0];
            expand_folds(init_expr);
            // [expr.prim.fold]/3: over an empty pack a binary fold yields
            // its init operand.
            irept result = init_expr;
            if(pack_on_right)
            {
              for(std::size_t i = 0; i < pack_args.size(); ++i)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(result);
                bin.get_sub().push_back(substitute_arg(pattern, pack_args[i]));
                result = bin;
              }
            }
            else
            {
              for(int i = static_cast<int>(pack_args.size()) - 1; i >= 0; --i)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(
                  substitute_arg(pattern, pack_args[std::size_t(i)]));
                bin.get_sub().push_back(result);
                result = bin;
              }
            }
            node = result;
            return;
          }
        }

        for(auto &s : node.get_sub())
          expand_folds(s);
        for(auto &ns : node.get_named_sub())
          expand_folds(ns.second);
      };

      irept &body = new_decl.type().add(ID_body);
      expand_folds(body);
    }

    // Expand variadic base classes: Bases... → Base0, Base1, ...
    if(
      new_decl.type().id() == ID_struct &&
      !template_type.template_parameters().empty() &&
      template_type.template_parameters().back().get_bool(ID_ellipsis))
    {
      irept &bases_irep = new_decl.type().add(ID_bases);
      irept::subt &bases_sub = bases_irep.get_sub();
      irept::subt expanded_bases;
      const std::size_t non_pack =
        template_type.template_parameters().size() - 1;

      // The trailing pack's deduced elements.  Prefer the template map
      // (the primary template's build() records them); for a PARTIAL
      // SPECIALIZATION with a non-identity pattern (e.g. libc++'s
      // `__tuple_impl<__tuple_indices<_Indx...>, _Tp...>`) the map holds
      // nothing, but the pattern re-deduction above (spec_bindings)
      // recorded them.
      const irep_idt trailing_pack_id =
        template_type.template_parameters().back().id() == ID_type
          ? template_type.template_parameters().back().type().get(ID_identifier)
          : template_type.template_parameters().back().get(ID_identifier);
      // Collect elements (types or non-type values) for EVERY bound
      // pack, keyed by its short name: the ellipsis'd base pattern may
      // reference not only the trailing pack but a LEADING one (libc++
      // __tuple_impl's `__tuple_leaf<_Indx>...` over the non-type index
      // pack of the partial specialization, [temp.variadic]/5.2).
      std::map<std::string, std::vector<typet>> pack_type_elems;
      std::map<std::string, std::vector<exprt>> pack_expr_elems;
      {
        auto shorten = [](const irep_idt &full_id) -> std::string
        {
          const std::string full = id2string(full_id);
          const auto pos = full.rfind("::");
          return pos != std::string::npos ? full.substr(pos + 2) : full;
        };
        for(const auto &tp : template_type.template_parameters())
        {
          if(!tp.get_bool(ID_ellipsis))
            continue;
          const irep_idt pid = tp.id() == ID_type ? tp.type().get(ID_identifier)
                                                  : tp.get(ID_identifier);
          if(pid.empty())
            continue;
          const std::string short_name = shorten(pid);
          auto pa = template_map.pack_args_map.find(pid);
          if(pa != template_map.pack_args_map.end())
            pack_type_elems[short_name] = pa->second;
          auto pe = template_map.pack_expr_map.find(pid);
          if(pe != template_map.pack_expr_map.end())
            pack_expr_elems[short_name] = pe->second;
        }
        for(const auto &entry : spec_bindings.get_sub())
        {
          const std::string short_name = shorten(entry.get(ID_identifier));
          if(
            entry.id() == "pack_types" &&
            pack_type_elems.find(short_name) == pack_type_elems.end())
          {
            for(const auto &t : entry.get_sub())
              pack_type_elems[short_name].push_back(
                static_cast<const typet &>(t));
          }
          else if(
            entry.id() == "pack_exprs" &&
            pack_expr_elems.find(short_name) == pack_expr_elems.end())
          {
            for(const auto &e : entry.get_sub())
              pack_expr_elems[short_name].push_back(
                static_cast<const exprt &>(e));
          }
        }
      }
      const std::string trailing_pack_short = [&]() -> std::string
      {
        const std::string full = id2string(trailing_pack_id);
        const auto pos = full.rfind("::");
        return pos != std::string::npos ? full.substr(pos + 2) : full;
      }();
      std::vector<typet> trailing_pack_elems;
      {
        auto it_t = pack_type_elems.find(trailing_pack_short);
        if(it_t != pack_type_elems.end())
          trailing_pack_elems = it_t->second;
      }

      for(auto &base : bases_sub)
      {
        // N5008 [temp.variadic]/5.2: a base-specifier pack expansion
        // (`leaf<T>...`, recorded by the parser via ID_ellipsis)
        // expands to one base-specifier per pack element, with the
        // element substituted into the pattern.  This covers patterns
        // that merely REFERENCE the pack (a template-id); the bare
        // `Pack...` shape keeps its established path below.
        // Which bound packs does this ellipsis'd base reference?  Per
        // N5008 [temp.variadic]/5 ALL packs named in the pattern expand
        // in LOCKSTEP (same length, /5 sentence 2); substituting only
        // the first-found pack left any parallel pack collapsed to its
        // scalar convenience element -- `__tuple_leaf<_Indx, _Tp>...`
        // instantiated as leaf<0,int>, leaf<1,int>, leaf<2,int> for
        // tuple<int,double,char> (coincidentally right for homogeneous
        // element types, wrong otherwise).
        std::vector<std::string> used_pack_shorts;
        if(base.get_bool(ID_ellipsis))
        {
          std::function<bool(const irept &, const std::string &)> refs_name =
            [&](const irept &n, const std::string &nm) -> bool
          {
            if(n.id() == ID_name && id2string(n.get(ID_identifier)) == nm)
              return true;
            for(const auto &c : n.get_sub())
              if(refs_name(c, nm))
                return true;
            for(const auto &c : n.get_named_sub())
              if(refs_name(c.second, nm))
                return true;
            return false;
          };
          for(const auto &pe : pack_type_elems)
            if(refs_name(base.find(ID_name), pe.first))
              used_pack_shorts.push_back(pe.first);
          for(const auto &pe : pack_expr_elems)
            if(refs_name(base.find(ID_name), pe.first))
              used_pack_shorts.push_back(pe.first);
        }
        const std::string used_pack_short =
          used_pack_shorts.empty() ? std::string{} : used_pack_shorts.front();
        const std::vector<typet> used_type_elems =
          pack_type_elems.count(used_pack_short)
            ? pack_type_elems[used_pack_short]
            : std::vector<typet>{};
        const std::vector<exprt> used_expr_elems =
          pack_expr_elems.count(used_pack_short)
            ? pack_expr_elems[used_pack_short]
            : std::vector<exprt>{};

        if(
          base.get_bool(ID_ellipsis) &&
          (!used_type_elems.empty() || !used_expr_elems.empty()))
        {
          std::function<bool(const irept &)> refs_pack = [&](const irept &n)
          {
            if(
              n.id() == ID_name &&
              id2string(n.get(ID_identifier)) == used_pack_short)
              return true;
            for(const auto &c : n.get_sub())
              if(refs_pack(c))
                return true;
            for(const auto &c : n.get_named_sub())
              if(refs_pack(c.second))
                return true;
            return false;
          };
          const bool bare_pack_base = [&]() -> bool
          {
            const irept &nm = base.find(ID_name);
            // bare `Pack...`: a cpp_name whose ONLY name component is
            // the pack and which has no template-argument list
            if(nm.id() != ID_cpp_name)
              return false;
            for(const auto &sub : nm.get_sub())
              if(sub.id() == ID_template_args)
                return false;
            return true;
          }();
          if(!bare_pack_base && refs_pack(base.find(ID_name)))
          {
            const std::size_t n_elems = !used_type_elems.empty()
                                          ? used_type_elems.size()
                                          : used_expr_elems.size();
            // [temp.variadic]/5: all packs of one expansion have equal
            // length; substitute EVERY referenced pack's elem_i-th
            // element in one pass.
            bool lockstep_ok = true;
            for(const auto &ps : used_pack_shorts)
            {
              const std::size_t len = pack_type_elems.count(ps)
                                        ? pack_type_elems[ps].size()
                                        : pack_expr_elems[ps].size();
              if(len != n_elems)
                lockstep_ok = false;
            }
            if(lockstep_ok)
            {
              for(std::size_t elem_i = 0; elem_i < n_elems; ++elem_i)
              {
                irept new_base = base;
                new_base.remove(ID_ellipsis);
                std::function<void(irept &)> subst = [&](irept &n)
                {
                  for(auto &c : n.get_sub())
                  {
                    // replace a cpp_name that IS a bare pack reference
                    if(c.id() == ID_cpp_name || c.id() == ID_ambiguous)
                    {
                      const irept &inner =
                        c.id() == ID_ambiguous ? c.find(ID_type) : c;
                      if(
                        inner.id() == ID_cpp_name &&
                        inner.get_sub().size() == 1 &&
                        inner.get_sub().front().id() == ID_name)
                      {
                        const std::string nm =
                          id2string(inner.get_sub().front().get(ID_identifier));
                        if(
                          std::find(
                            used_pack_shorts.begin(),
                            used_pack_shorts.end(),
                            nm) != used_pack_shorts.end())
                        {
                          exprt elem_arg;
                          if(pack_type_elems.count(nm))
                          {
                            elem_arg = exprt(ID_type);
                            elem_arg.type() = pack_type_elems[nm][elem_i];
                          }
                          else
                            elem_arg = pack_expr_elems[nm][elem_i];
                          c = elem_arg;
                          continue;
                        }
                      }
                    }
                    subst(c);
                  }
                  for(auto &c : n.get_named_sub())
                    subst(c.second);
                };
                subst(new_base);
                expanded_bases.push_back(new_base);
              }
              continue;
            }
          }
        }
        // Check if this base references the pack parameter
        const irept &base_name = base.find(ID_name);
        bool is_pack_base = false;
        if(base_name.id() == ID_cpp_name)
        {
          for(const auto &sub : base_name.get_sub())
          {
            if(sub.id() == ID_name)
            {
              // Check if this name matches the pack parameter
              const auto &pack_param =
                template_type.template_parameters().back();
              const std::string full_id =
                id2string(pack_param.type().get(ID_identifier));
              auto pos = full_id.rfind("::");
              const std::string pack_name =
                pos != std::string::npos ? full_id.substr(pos + 2) : full_id;
              if(id2string(sub.get(ID_identifier)) == pack_name)
                is_pack_base = true;
              break;
            }
          }
        }

        if(is_pack_base)
        {
          // Expand: create one base for each pack argument
          for(std::size_t k = non_pack;
              k < full_template_args.arguments().size();
              ++k)
          {
            const exprt &arg = full_template_args.arguments()[k];
            if(arg.id() == ID_type)
            {
              irept new_base = base;
              // Replace the name with the concrete type
              const std::string tag_id =
                id2string(arg.type().get(ID_identifier));
              // Strip "tag-" prefix to get the class name
              std::string class_name = tag_id;
              if(class_name.substr(0, 4) == "tag-")
                class_name = class_name.substr(4);
              irept new_name(ID_cpp_name);
              irept name_sub(ID_name);
              name_sub.set(ID_identifier, class_name);
              new_name.get_sub().push_back(name_sub);
              new_base.add(ID_name) = new_name;
              expanded_bases.push_back(new_base);
            }
          }
        }
        else
        {
          expanded_bases.push_back(base);
        }
      }
      bases_sub = expanded_bases;
    }

    // Also apply template map to declarator types (function parameters)
    for(auto &d : new_decl.declarators())
      template_map.apply(d.type());
  }

  if(new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
  {
    // Before instantiating from the primary template, check if there is
    // a full specialization (template<>) that matches the template
    // arguments. If so, use the specialization instead.
    if(
      !specialization_given &&
      template_symbol.type.get(ID_specialization_of).empty())
    {
      cpp_scopet &parent_scope = template_scope->get_parent();
      cpp_scopet::id_sett id_set =
        parent_scope.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

      for(const auto *id_ptr : id_set)
      {
        const symbolt &s = lookup(id_ptr->identifier);
        if(s.type.get(ID_specialization_of).empty())
          continue;

        const cpp_declarationt &spec_decl = to_cpp_declaration(s.type);
        // Only consider full specializations (zero template parameters)
        if(!spec_decl.template_type().template_parameters().empty())
          continue;

        const cpp_template_args_non_tct &spec_args =
          spec_decl.partial_specialization_args();
        if(
          spec_args.arguments().size() != full_template_args.arguments().size())
        {
          continue;
        }

        // Typecheck the specialization args and compare
        cpp_saved_template_mapt saved_map2(template_map);
        cpp_save_scopet save_scope2(cpp_scopes);
        cpp_template_args_tct spec_args_tc;
        bool match = false;
        try
        {
          spec_args_tc = typecheck_template_args(
            source_location, template_symbol, spec_args);
          match = (spec_args_tc.arguments() == full_template_args.arguments());
        }
        catch(...)
        {
        }

        if(match)
        {
          // Re-instantiate using the full specialization
          return instantiate_template(
            source_location, s, spec_args_tc, full_template_args);
        }
      }
    }

    // Switch to the sub-scope so that typecheck_compound_type creates
    // the class symbol with an identifier that includes the template
    // suffix, matching the identifier used by class_template_symbol.
    cpp_scopes.go_to(sub_scope);

    // a class template
    // Apply template map to static member initializers in the class
    // body to substitute non-type template parameters before processing.
    if(new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
    {
      irept &body = new_decl.type().add(ID_body);
      for(auto &member : body.get_sub())
      {
        if(member.id() != ID_cpp_declaration)
          continue;
        for(auto &sub : member.get_sub())
        {
          if(sub.id() == ID_cpp_declarator)
          {
            exprt &val = static_cast<exprt &>(sub.add(ID_value));
            if(val.is_not_nil())
              template_map.apply(val);
          }
        }
      }
    }
    // Per [temp.variadic]/5: remove empty pack expansions
    if(
      id2string(template_symbol.name).find("_Compressed_pair") !=
        std::string::npos &&
      id2string(template_symbol.name).find("_Zero") != std::string::npos)
    {
      if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
      {
        std::set<std::string> ep_names;
        for(const auto &ps : template_map.pack_size_map)
        {
          if(ps.second == 0)
          {
            const std::string full = id2string(ps.first);
            auto pos = full.rfind("::");
            ep_names.insert(
              pos != std::string::npos ? full.substr(pos + 2) : full);
          }
        }
        if(!ep_names.empty())
        {
          auto &dt = new_decl.declarators()[0].type();
          if(dt.id() == ID_function_type)
          {
            irept &params = dt.add(ID_parameters);
            params.get_sub().erase(
              std::remove_if(
                params.get_sub().begin(),
                params.get_sub().end(),
                [](const irept &p)
                {
                  if(p.id() != ID_cpp_declaration)
                    return false;
                  for(const auto &d : p.get_sub())
                    if(
                      d.id() == ID_cpp_declarator &&
                      (d.find(ID_type).get_bool(ID_ellipsis) ||
                       d.get_bool(ID_ellipsis)))
                      return true;
                  return false;
                }),
              params.get_sub().end());
          }
          // Per [temp.variadic]/7: remove pack expansion expressions.
          // After template_map.apply(), pack params may appear as
          // template_parameter_symbol_typet or as ID_name nodes.
          std::function<bool(const irept &)> has_ep =
            [&](const irept &n) -> bool
          {
            if(
              n.id() == ID_name &&
              ep_names.count(id2string(n.get(ID_identifier))))
              return true;
            // Check template_parameter_symbol_typet
            if(n.id() == ID_template_parameter_symbol_type)
            {
              const std::string full = id2string(n.get(ID_identifier));
              auto pos = full.rfind("::");
              const std::string sn =
                pos != std::string::npos ? full.substr(pos + 2) : full;
              if(ep_names.count(sn))
                return true;
            }
            // Check type sub for template_parameter_symbol_typet
            const auto &type_sub = n.find(ID_type);
            if(
              type_sub.is_not_nil() &&
              type_sub.id() == ID_template_parameter_symbol_type)
            {
              const std::string full = id2string(type_sub.get(ID_identifier));
              auto pos = full.rfind("::");
              const std::string sn =
                pos != std::string::npos ? full.substr(pos + 2) : full;
              if(ep_names.count(sn))
                return true;
            }
            for(const auto &s : n.get_sub())
              if(has_ep(s))
                return true;
            for(const auto &ns : n.get_named_sub())
              if(has_ep(ns.second))
                return true;
            return false;
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          for(auto &init : mi.get_sub())
          {
            auto &subs = init.get_sub();
            subs.erase(
              std::remove_if(
                subs.begin(),
                subs.end(),
                [&](const irept &s) { return has_ep(s); }),
              subs.end());
          }
        }
      }
    }

    convert_non_template_declaration(new_decl);

    // Propagate template info to the class symbol so that member
    // function template bodies can find the class template parameters.
    {
      std::string inst_suffix = template_suffix(full_template_args);
      irep_idt class_sym_id = id2string(sub_scope.prefix) + "tag-" +
                              id2string(template_symbol.base_name) +
                              inst_suffix;
      if(auto *cs = symbol_table.get_writeable(class_sym_id))
      {
        if(cs->type.find(ID_C_template).is_nil())
        {
          cs->type.set(
            ID_C_template,
            to_cpp_declaration(template_symbol.type).template_type());
          cs->type.set(ID_C_template_arguments, specialization_template_args);
        }
        if(
          !spec_bindings.get_sub().empty() &&
          cs->type.find(irep_idt{"#spec_template_packs"}).is_nil())
        {
          cs->type.set(irep_idt{"#spec_template_packs"}, spec_bindings);
        }
      }
    }

    // Restore the template scope for template method processing.
    saved_scope.restore();
    cpp_scopes.go_to(*template_scope);

    // also instantiate all the template methods
    const exprt &template_methods = static_cast<const exprt &>(
      template_symbol.value.find(ID_template_methods));

    for(auto &tm : template_methods.operands())
    {
      saved_scope.restore();

      // A class template's members -- including those defined out of line --
      // are instantiated in the context of the (instantiated) class
      // ([temp.inst]/2, [basic.lookup.unqual], [dcl.meaning]): unqualified name
      // lookup in a member must reach the class's own members and, through the
      // class's enclosing namespace, namespace-scope names.
      // typecheck_template_parameters below creates the method's template scope
      // under the current scope, so enter the instantiated class's scope first.
      // Merely restoring the scope that first triggered the instantiation (e.g.
      // a function body, as when overload resolution instantiates the class)
      // would look names up there instead -- a namespace-scope name in an
      // out-of-line member's return type would not be found -- while entering
      // only the template-parameter scope would miss the class's own members.
      const irep_idt inst_class_name = new_decl.type().get(ID_identifier);
      auto inst_scope_it = cpp_scopes.id_map.find(inst_class_name);
      if(!inst_class_name.empty() && inst_scope_it != cpp_scopes.id_map.end())
        cpp_scopes.go_to(*inst_scope_it->second);
      else
        cpp_scopes.go_to(*template_scope);

      cpp_declarationt method_decl =
        static_cast<const cpp_declarationt &>(static_cast<const irept &>(tm));

      // Member class/union templates are already instantiated as part
      // of the class body by convert_non_template_declaration above.
      if(method_decl.is_class_template())
        continue;

      // Member template aliases (e.g., template<typename U> using X = ...)
      // are already handled during class body conversion. Skip them here
      // to avoid resolving their template parameters in the wrong scope.
      if(method_decl.is_template_alias())
      {
        continue;
      }

      // copy the type of the template method
      template_typet method_type = method_decl.template_type();

      // If this method has more template parameters than the class
      // template, it is a member function template (e.g.,
      // template<T> template<U> void S<T>::f(U x) {}).
      // Skip it during class instantiation — it will be instantiated
      // when actually called.
      // Also skip methods with fewer template parameters — these belong
      // to a partial specialization (e.g., vector<bool, _Alloc> has 1
      // parameter vs the primary vector<T, _Alloc> with 2).
      const std::size_t n_class_params =
        specialization_template_args.arguments().size();
      const std::size_t n_method_params =
        method_type.template_parameters().size();

      if(n_method_params != n_class_params)
      {
        // Member function template — register in the instantiated
        // class scope so operator overload resolution can find it.
        if(!method_decl.declarators().empty())
        {
          const irep_idt &base_name =
            method_decl.declarators().front().name().get_base_name();
          if(!base_name.empty())
          {
            std::string inst_suffix = template_suffix(full_template_args);
            irep_idt class_id = id2string(sub_scope.prefix) + "tag-" +
                                id2string(template_symbol.base_name) +
                                inst_suffix;
            auto it = cpp_scopes.id_map.find(class_id);
            if(it != cpp_scopes.id_map.end())
            {
              // Find the template symbol in the original class scope
              // Search the template scope and its immediate children
              // (the class body scope) for the member function template.
              auto tmpl_results = template_scope->lookup(
                base_name,
                cpp_scopet::SCOPE_ONLY,
                cpp_idt::id_classt::TEMPLATE);
              if(tmpl_results.empty())
              {
                // Search children (class body scope)
                tmpl_results = template_scope->lookup(
                  base_name,
                  cpp_scopet::QUALIFIED,
                  cpp_idt::id_classt::TEMPLATE);
              }
              for(auto *tmpl_id : tmpl_results)
              {
                auto &cs = static_cast<cpp_scopet &>(*it->second);
                cpp_idt &new_id = cs.insert(base_name);
                new_id.id_class = cpp_idt::id_classt::TEMPLATE;
                new_id.identifier = tmpl_id->identifier;
                new_id.is_member = true;
                break;
              }
            }
          }
        }
        continue;
      }

      // Skip methods whose class qualifier contains concrete template
      // arguments that don't match the current instantiation. This
      // filters out methods of partial specializations (e.g.,
      // vector<bool, _Alloc>::_M_insert_range) when instantiating the
      // primary template (e.g., vector<unsigned int, allocator<...>>).
      if(!method_decl.declarators().empty())
      {
        const auto &name = method_decl.declarators().front().name();
        bool skip = false;
        for(const auto &sub : name.get_sub())
        {
          if(sub.id() != ID_template_args)
            continue;
          const auto &targs = sub.find(ID_arguments).get_sub();
          for(std::size_t i = 0;
              i < targs.size() && i < full_template_args.arguments().size();
              i++)
          {
            // Template arguments that are template parameter names
            // (cpp_name) are not concrete — skip those.
            const irept *t = &targs[i];
            if(t->id() == ID_type)
              t = &t->find(ID_type);
            if(t->id() == ID_ambiguous)
              t = &t->find(ID_type);
            if(t->id() == ID_cpp_name || t->id() == ID_nil || t->id().empty())
              continue;
            // This is a concrete type. Convert and compare.
            const auto &full_arg = full_template_args.arguments()[i];
            if(full_arg.id() != ID_type)
              continue;
            typet concrete = static_cast<const typet &>(*t);
            try
            {
              cpp_convert_plain_type(concrete, get_message_handler());
            }
            catch(...)
            {
              continue;
            }
            if(concrete != full_arg.type())
            {
              skip = true;
              break;
            }
          }
          break;
        }
        if(skip)
          continue;
      }

      // do template parameters
      // this also sets up the template scope of the method
      cpp_scopet &method_scope = typecheck_template_parameters(method_type);

      cpp_scopes.go_to(method_scope);

      // mapping from template arguments to values/types
      template_map.build(method_type, specialization_template_args);
#ifdef DEBUG
      std::cout << "METHOD MAP:\n";
      template_map.print(std::cout);
#endif

      method_decl.remove(ID_template_type);
      method_decl.remove(ID_is_template);

      // Apply the template map to substitute template parameters
      // (e.g. _Dom, _Tp) with the actual types in the method
      // declaration before converting it.
      // First, type-check the declaration type in the method's
      // template scope so that template parameter names (cpp_name)
      // are resolved to template_parameter_symbol_type, then apply
      // the template map to replace them with actual types.
      // Add the class scope as a using scope so that class-scoped
      // names (e.g., typedefs like 'iterator' in trailing return
      // types) can also be resolved.
      if(method_decl.type().id() == ID_cpp_name)
      {
        const irep_idt &inst_class_name = new_decl.type().get(ID_identifier);
        if(!inst_class_name.empty())
        {
          cpp_scopet &class_scope = cpp_scopes.get_scope(inst_class_name);
          method_scope.add_using_scope(class_scope);
        }
        typecheck_type(method_decl.type());
        template_map.apply(method_decl.type());
      }

      convert(method_decl);
    }

    const irep_idt &new_symb_id = new_decl.type().get(ID_identifier);

    // Move deferred methods of this class to method_bodies.
    // Methods are added to deferred_typechecking during class body
    // processing because the parent scope is a template scope.
    {
      std::string class_name = id2string(new_symb_id);
      // Strip the "tag-" marker that precedes the unqualified
      // class name in the symbol-table id of a class-template
      // instantiation.  The id has the form
      //   `[ns1::...::nsN::]tag-Name<args>`,
      // so the `tag-` token sits after the last `::` PRECEDING the
      // template-argument list -- `args` may themselves contain `::`
      // (e.g. `std::__detail::tag-_Hashtable_traits<0,1,1>` inside
      // `_Insert<...>`), so an unbounded rfind("::") would land inside
      // an argument, the wrong (or no) `tag-` would be stripped, and
      // the substring match below would MISS every deferred member:
      // the instance's inline member bodies would then be nil'd by
      // clean_up and calls to them havoc'd (unordered_set::insert was
      // a no-op).  Same shape as queue_deferred_methods_of_instance.
      // The deferred method ids are stored without the `tag-` token
      // (e.g. `ns::Name<args>::method(this)`), so we need a class_name
      // in the same shape for the substring match below to succeed.
      std::size_t lt_pos = class_name.find('<');
      std::size_t search_end =
        lt_pos == std::string::npos ? std::string::npos : lt_pos;
      auto last_sep = class_name.rfind("::", search_end);
      std::size_t tag_pos = last_sep != std::string::npos ? last_sep + 2 : 0;
      if(class_name.compare(tag_pos, 4, "tag-") == 0)
        class_name.erase(tag_pos, 4);
      class_name += "::";
      std::vector<irep_idt> to_move;
      for(const auto &d : deferred_typechecking)
      {
        if(id2string(d).find(class_name) != std::string::npos)
          to_move.push_back(d);
      }
      for(const auto &d : to_move)
      {
        deferred_typechecking.erase(d);
        auto *sym = symbol_table.get_writeable(d);
        if(!sym)
          continue;

        // If the method has nil body, check if a body is available
        // from template_methods (out-of-class definitions in .tcc).
        // Search ALL template symbols, not just the current one.
        if(sym->value.is_nil() && sym->type.id() == ID_code)
        {
          for(const auto &tsp : symbol_table)
          {
            if(!tsp.second.type.get_bool(ID_is_template))
              continue;
            if(tsp.second.value.is_nil())
              continue;
            const exprt &tms = static_cast<const exprt &>(
              tsp.second.value.find(ID_template_methods));
            for(const auto &tm : tms.operands())
            {
              const cpp_declarationt &md =
                static_cast<const cpp_declarationt &>(
                  static_cast<const irept &>(tm));
              if(md.declarators().empty())
                continue;
              if(md.declarators()[0].name().get_base_name() != sym->base_name)
                continue;
              if(md.declarators()[0].find(ID_value).is_nil())
                continue;
              // Found body. Apply class template substitution.
              const template_typet &md_tt = md.template_type();
              std::size_t n_md = md_tt.template_parameters().size();
              std::size_t n_cls =
                specialization_template_args.arguments().size();
              if(n_md <= n_cls)
              {
                // Regular method: substitute all params
                exprt body = static_cast<const exprt &>(
                  md.declarators()[0].find(ID_value));
                cpp_saved_template_mapt sm(template_map);
                template_map.build(md_tt, specialization_template_args);
                template_map.apply(body);
                // Per [temp.variadic]/7: remove empty pack
                // expansion expressions from the body.
                if(!template_map.pack_size_map.empty())
                {
                  std::set<std::string> ep;
                  for(const auto &ps : template_map.pack_size_map)
                    if(ps.second == 0)
                    {
                      const std::string f = id2string(ps.first);
                      auto p = f.rfind("::");
                      ep.insert(p != std::string::npos ? f.substr(p + 2) : f);
                    }
                  if(!ep.empty())
                  {
                    std::function<bool(const irept &)> has_ep =
                      [&](const irept &n) -> bool
                    {
                      if(n.id() == ID_template_parameter_symbol_type)
                      {
                        const std::string f = id2string(n.get(ID_identifier));
                        auto p = f.rfind("::");
                        if(ep.count(
                             p != std::string::npos ? f.substr(p + 2) : f))
                          return true;
                      }
                      if(
                        n.id() == ID_name &&
                        ep.count(id2string(n.get(ID_identifier))))
                        return true;
                      for(const auto &s : n.get_sub())
                        if(has_ep(s))
                          return true;
                      for(const auto &ns : n.get_named_sub())
                        if(has_ep(ns.second))
                          return true;
                      return false;
                    };
                    // Remove from member_initializers in body
                    irept &mi = body.add(ID_member_initializers);
                    for(auto &init : mi.get_sub())
                    {
                      auto &subs = init.get_sub();
                      subs.erase(
                        std::remove_if(
                          subs.begin(),
                          subs.end(),
                          [&](const irept &s) { return has_ep(s); }),
                        subs.end());
                    }
                  }
                }
                sym->value = body;
              }
              else
              {
                // Member function template: substitute class params,
                // deduce method params from concrete function sig.
                exprt body = static_cast<const exprt &>(
                  md.declarators()[0].find(ID_value));
                // Build full args: class args + deduced method args
                cpp_template_args_tct full;
                for(const auto &a : specialization_template_args.arguments())
                  full.arguments().push_back(a);
                // Deduce method params from function signature
                const code_typet &cft = to_code_type(sym->type);
                const auto &cps = cft.parameters();
                std::size_t off = (!cps.empty() && cps[0].get_this()) ? 1 : 0;
                for(std::size_t i = n_cls; i < n_md; i++)
                {
                  exprt a(ID_type);
                  if(off < cps.size())
                    a.type() = cps[off].type();
                  else
                    a.type() = typet(ID_empty);
                  full.arguments().push_back(a);
                }
                cpp_saved_template_mapt sm(template_map);
                template_map.build(md_tt, full);
                template_map.apply(body);
                // Per [temp.variadic]/7: remove empty pack
                // expansion expressions from the body.
                if(!template_map.pack_size_map.empty())
                {
                  std::set<std::string> ep;
                  for(const auto &ps : template_map.pack_size_map)
                    if(ps.second == 0)
                    {
                      const std::string f = id2string(ps.first);
                      auto p = f.rfind("::");
                      ep.insert(p != std::string::npos ? f.substr(p + 2) : f);
                    }
                  if(!ep.empty())
                  {
                    std::function<bool(const irept &)> has_ep =
                      [&](const irept &n) -> bool
                    {
                      if(n.id() == ID_template_parameter_symbol_type)
                      {
                        const std::string f = id2string(n.get(ID_identifier));
                        auto p = f.rfind("::");
                        if(ep.count(
                             p != std::string::npos ? f.substr(p + 2) : f))
                          return true;
                      }
                      if(
                        n.id() == ID_name &&
                        ep.count(id2string(n.get(ID_identifier))))
                        return true;
                      for(const auto &s : n.get_sub())
                        if(has_ep(s))
                          return true;
                      for(const auto &ns : n.get_named_sub())
                        if(has_ep(ns.second))
                          return true;
                      return false;
                    };
                    // Remove from member_initializers in body
                    irept &mi = body.add(ID_member_initializers);
                    for(auto &init : mi.get_sub())
                    {
                      auto &subs = init.get_sub();
                      subs.erase(
                        std::remove_if(
                          subs.begin(),
                          subs.end(),
                          [&](const irept &s) { return has_ep(s); }),
                        subs.end());
                    }
                  }
                }
                // Also copy member initializers into the body
                // so the method body pass can process them.
                // Remove empty pack expressions per [temp.variadic]/7.
                const irept &mi_src =
                  md.declarators()[0].find(ID_member_initializers);
                if(mi_src.is_not_nil())
                {
                  irept mi_copy = mi_src;
                  if(!template_map.pack_size_map.empty())
                  {
                    std::set<std::string> ep2;
                    for(const auto &ps : template_map.pack_size_map)
                      if(ps.second == 0)
                      {
                        const std::string f = id2string(ps.first);
                        auto p = f.rfind("::");
                        ep2.insert(
                          p != std::string::npos ? f.substr(p + 2) : f);
                      }
                    if(!ep2.empty())
                    {
                      std::function<bool(const irept &)> has_ep2 =
                        [&](const irept &n) -> bool
                      {
                        if(n.id() == ID_template_parameter_symbol_type)
                        {
                          const std::string f = id2string(n.get(ID_identifier));
                          auto p = f.rfind("::");
                          if(ep2.count(
                               p != std::string::npos ? f.substr(p + 2) : f))
                            return true;
                        }
                        if(
                          n.id() == ID_name &&
                          ep2.count(id2string(n.get(ID_identifier))))
                          return true;
                        for(const auto &s : n.get_sub())
                          if(has_ep2(s))
                            return true;
                        for(const auto &ns : n.get_named_sub())
                          if(has_ep2(ns.second))
                            return true;
                        return false;
                      };
                      for(auto &init : mi_copy.get_sub())
                      {
                        auto &subs = init.get_sub();
                        subs.erase(
                          std::remove_if(
                            subs.begin(),
                            subs.end(),
                            [&](const irept &s) { return has_ep2(s); }),
                          subs.end());
                      }
                    }
                  }
                  body.add(ID_member_initializers) = mi_copy;
                }
                sym->value = body;
              }
              goto body_found;
            }
          }
        body_found:
        {
        }
        }

        add_method_body(sym);
      }
    }

    symbolt &new_symb = symbol_table.get_writeable_ref(new_symb_id);

    // add template arguments to type in order to retrieve template map when
    // typechecking function body
    new_symb.type.set(ID_C_template, template_type);
    new_symb.type.set(
      ID_C_template_arguments,
      record_full_template_args ? full_template_args
                                : specialization_template_args);

#ifdef DEBUG
    std::cout << "instance symbol: " << new_symb.name << "\n\n";
    std::cout << "template type: " << template_type.pretty() << "\n\n";
#endif

    return new_symb;
  }

  if(is_template_method && !new_decl.is_typedef())
  {
    // gates the concretized-pack-pattern fallback (see cpp_typecheck.h)
    const bool saved_imft = instantiating_member_function_template;
    instantiating_member_function_template = true;
    struct imft_guardt
    {
      bool &flag;
      bool saved;
      ~imft_guardt()
      {
        flag = saved;
      }
    } imft_guard{instantiating_member_function_template, saved_imft};
    // Apply template_map to parameter types for SFINAE substitution
    for(auto &d : new_decl.declarators())
      template_map.apply(d.type());
    symbolt &symb = symbol_table.get_writeable_ref(class_name);

    if(new_decl.declarators().size() != 1)
    {
      error().source_location = source_location;
      error() << "expected exactly one declarator in template" << eom;
      throw 0;
    }

    if(new_decl.member_spec().is_virtual())
    {
      error().source_location = new_decl.source_location();
      error() << "invalid use of `virtual' in template declaration" << eom;
      throw 0;
    }

    if(
      new_decl.storage_spec().is_extern() ||
      new_decl.storage_spec().is_register() ||
      new_decl.storage_spec().is_mutable())
    {
      error().source_location = new_decl.source_location();
      error() << "invalid storage class specified for template field" << eom;
      throw 0;
    }

    // In C++11, 'auto' in a template member declaration indicates a
    // trailing return type. Only reject it when there are no declarators.
    if(new_decl.storage_spec().is_auto() && new_decl.declarators().empty())
    {
      error().source_location = new_decl.source_location();
      error() << "invalid storage class specified for template field" << eom;
      throw 0;
    }

    bool is_static = new_decl.storage_spec().is_static();
    irep_idt access = new_decl.get(ID_C_access);

    CHECK_RETURN(!access.empty());
    PRECONDITION(symb.type.id() == ID_struct || symb.type.id() == ID_union);

    // If the method declaration has no body, check if the body was
    // provided by an out-of-class definition (stored in template_methods
    // of the class template).
    if(new_decl.declarators()[0].find(ID_value).is_nil())
    {
      // Find the class template symbol
      for(const auto &sp : symbol_table)
      {
        if(
          sp.second.type.get_bool(ID_is_template) &&
          sp.second.value.is_not_nil())
        {
          // Match by base name OR by checking if this template's
          // instantiated_with includes the current class.
          if(sp.second.base_name != symb.base_name)
            continue;
          const exprt &tmethods = static_cast<const exprt &>(
            sp.second.value.find(ID_template_methods));
          if(tmethods.operands().empty())
            continue;
          irep_idt method_base =
            new_decl.declarators()[0].name().get_base_name();
          for(const auto &tm : tmethods.operands())
          {
            const cpp_declarationt &md = static_cast<const cpp_declarationt &>(
              static_cast<const irept &>(tm));
            if(md.declarators().empty())
              continue;
            if(md.declarators()[0].name().get_base_name() != method_base)
              continue;
            if(md.declarators()[0].find(ID_value).is_nil())
              continue;
            // Verify this is a member function template
            const template_typet &md_tt = md.template_type();
            if(
              md_tt.template_parameters().size() <=
              specialization_template_args.arguments().size())
              continue;
            // N5008 [over.load], [dcl.fct]/3: the definition belonging to
            // this member is the one whose SIGNATURE matches; matching by
            // base name alone confuses same-named overloaded member
            // templates (std::pair's two piecewise constructors: the
            // 3-parameter delegating one and its 4-parameter target).
            // Compare the function parameter count as a cheap faithful
            // discriminator (the parameter TYPES are unsubstituted
            // cpp_names on both sides and cannot be compared directly).
            {
              const typet &d_ftype = new_decl.declarators()[0].type();
              const typet &m_ftype = md.declarators()[0].type();
              if(
                d_ftype.id() == ID_function_type &&
                m_ftype.id() == ID_function_type &&
                d_ftype.find(ID_parameters).get_sub().size() !=
                  m_ftype.find(ID_parameters).get_sub().size())
                continue;
            }
            // Copy the body. The body is in parsed (not type-checked)
            // form. It will be type-checked by typecheck_method_bodies
            // with the proper template map.
            new_decl.declarators()[0].add(ID_value) =
              md.declarators()[0].find(ID_value);

            // N5008 [class.base.init]/1: the ctor-initializer is part of
            // the constructor's DEFINITION.  An out-of-line delegating
            // constructor template (std::pair's piecewise constructor in
            // <tuple>, `: pair(__first, __second,
            // _Build_index_tuple<...>::__type(), ...)`) keeps its
            // mem-initializer-list on the definition's declarator; without
            // copying it the instantiated member converts with NO
            // initializer -- members default-initialized, the delegation
            // never happens, and the constructed object keeps garbage
            // (std::map's first insert stored a garbage key).
            {
              const irept &m_inits =
                md.declarators()[0].find(ID_member_initializers);
              if(m_inits.is_not_nil())
                new_decl.declarators()[0].member_initializers() = m_inits;
            }

            // [dcl.fct]/3: parameter names are not part of the function
            // type, so an out-of-line definition may name its parameters
            // differently from the in-class declaration (e.g. libstdc++
            // declares `_M_insert_unique(_Arg&& __x)` but defines it with
            // `_Arg&& __v`).  The body we just adopted comes from the
            // definition and refers to the definition's parameter names,
            // whereas new_decl's signature was built from the declaration.
            // Adopt the definition's parameter names so the body's
            // references resolve when the body is type-checked; otherwise
            // the unresolved names make the body ill-formed, and for a
            // system-header body it would be silently dropped, leaving the
            // member function with no body (so the call returns nondet).
            {
              typet &inst_type = new_decl.declarators()[0].type();
              const typet &def_type = md.declarators()[0].type();
              if(
                inst_type.id() == ID_function_type &&
                def_type.id() == ID_function_type)
              {
                auto &ip = inst_type.add(ID_parameters).get_sub();
                const auto &dp = def_type.find(ID_parameters).get_sub();
                std::size_t j = 0;
                for(auto &pi : ip)
                {
                  if(pi.id() != ID_cpp_declaration)
                    continue;
                  while(j < dp.size() && dp[j].id() != ID_cpp_declaration)
                    ++j;
                  if(j >= dp.size())
                    break;
                  auto &ipd = static_cast<cpp_declarationt &>(pi);
                  const auto &dpd =
                    static_cast<const cpp_declarationt &>(dp[j]);
                  ++j;
                  if(!ipd.declarators().empty() && !dpd.declarators().empty())
                    ipd.declarators().front().name() =
                      dpd.declarators().front().name();
                }
              }
            }
            goto body_found_is_tm;
          }
          continue;
        }
      }
    body_found_is_tm:
    {
    }
    }

    // Per [temp.variadic]/5: set pack_size_map and remove empty
    // pack expansions for function template members.
    if(new_decl.is_template())
    {
      const auto &fn_params = new_decl.template_type().template_parameters();
      for(const auto &p : fn_params)
      {
        if(p.get_bool(ID_ellipsis))
        {
          irep_idt pid = p.type().get(ID_identifier);
          // N5008 [temp.variadic]/7: a pack is empty only when it is
          // bound to zero elements.  A pack of TWO or more elements has
          // no scalar type_map entry (deliberately -- see build()), only
          // a pack_args_map binding; checking type_map alone declared
          // every such pack empty, and the removal below then deleted
          // the `_Args&&...` parameter of e.g. vector<pair<T,U>>::
          // emplace_back(t, u) whose deduced pack is heterogeneous --
          // the signature degenerated and every call failed
          // "found no match".
          if(
            !pid.empty() &&
            template_map.type_map.find(pid) == template_map.type_map.end() &&
            template_map.pack_args_map.find(pid) ==
              template_map.pack_args_map.end() &&
            template_map.pack_expr_map.find(pid) ==
              template_map.pack_expr_map.end() &&
            template_map.pack_size_map.find(pid) ==
              template_map.pack_size_map.end())
          {
            template_map.pack_size_map[pid] = 0;
          }
        }
      }
      if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
      {
        std::set<std::string> ep_names;
        for(const auto &ps : template_map.pack_size_map)
          if(ps.second == 0)
          {
            const std::string f = id2string(ps.first);
            auto p = f.rfind("::");
            ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
          }
        if(!ep_names.empty())
        {
          // Remove pack params from function type
          auto &dt = new_decl.declarators()[0].type();
          if(dt.id() == ID_function_type)
          {
            irept &params = dt.add(ID_parameters);
            params.get_sub().erase(
              std::remove_if(
                params.get_sub().begin(),
                params.get_sub().end(),
                [&](const irept &p)
                {
                  if(p.id() != ID_cpp_declaration)
                    return false;
                  for(const auto &d : p.get_sub())
                  {
                    if(
                      d.id() == ID_cpp_declarator &&
                      (d.find(ID_type).get_bool(ID_ellipsis) ||
                       d.get_bool(ID_ellipsis)))
                    {
                      // N5008 [temp.variadic]/7 applies per pack: with
                      // MULTIPLE template parameter packs (libc++
                      // __tuple_impl's five-pack constructor), remove the
                      // function parameter pack only when ITS OWN pack is
                      // among the empty ones -- `_Up&&... __u` (two
                      // elements) must survive `_Ul`/`_Tl` being empty.
                      const auto &pd = static_cast<const cpp_declarationt &>(p);
                      const irept *t = &static_cast<const irept &>(pd.type());
                      while(t->id() != ID_cpp_name && !t->get_sub().empty())
                        t = &t->get_sub().front();
                      std::string own;
                      if(t->id() == ID_cpp_name && !t->get_sub().empty())
                        own =
                          id2string(t->get_sub().front().get(ID_identifier));
                      return own.empty() || ep_names.count(own) != 0;
                    }
                    // Also check for template_parameter_symbol_typet
                    // referencing empty pack
                    const auto &dtype = d.find(ID_type);
                    if(dtype.id() == ID_template_parameter_symbol_type)
                    {
                      const std::string f = id2string(dtype.get(ID_identifier));
                      auto pos = f.rfind("::");
                      if(ep_names.count(
                           pos != std::string::npos ? f.substr(pos + 2) : f))
                        return true;
                    }
                  }
                  // Check the type sub of the declaration
                  const auto &ptype = p.find(ID_type);
                  if(ptype.id() == ID_template_parameter_symbol_type)
                  {
                    const std::string f = id2string(ptype.get(ID_identifier));
                    auto pos = f.rfind("::");
                    if(ep_names.count(
                         pos != std::string::npos ? f.substr(pos + 2) : f))
                      return true;
                  }
                  return false;
                }),
              params.get_sub().end());
          }
          // Remove member initializer expressions with empty pack
          std::function<bool(const irept &)> has_ep =
            [&](const irept &n) -> bool
          {
            if(n.id() == ID_template_parameter_symbol_type)
            {
              const std::string f = id2string(n.get(ID_identifier));
              auto p = f.rfind("::");
              if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
                return true;
            }
            if(
              n.id() == ID_name &&
              ep_names.count(id2string(n.get(ID_identifier))))
              return true;
            const auto &tsub = n.find(ID_type);
            if(tsub.is_not_nil() && has_ep(tsub))
              return true;
            for(const auto &s : n.get_sub())
              if(has_ep(s))
                return true;
            for(const auto &ns : n.get_named_sub())
              if(ns.first != ID_type && has_ep(ns.second))
                return true;
            return false;
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          for(auto &init : mi.get_sub())
          {
            auto &subs = init.get_sub();
            subs.erase(
              std::remove_if(
                subs.begin(),
                subs.end(),
                [&](const irept &s) { return has_ep(s); }),
              subs.end());
          }
        }
      }
      // Per [temp.variadic]/7: for non-empty packs, substitute
      // pack parameter names with actual types.
      if(!template_map.pack_args_map.empty() && !new_decl.declarators().empty())
      {
        std::map<std::string, irep_idt> pack_subst;
        for(const auto &pa : template_map.pack_args_map)
        {
          // N5008 [temp.variadic]/5: single-element packs only -- see the
          // guarded mem-init substitution above.
          if(pa.second.size() != 1)
            continue;
          const std::string full = id2string(pa.first);
          auto p = full.rfind("::");
          const std::string sn =
            p != std::string::npos ? full.substr(p + 2) : full;
          const typet &t = pa.second.front();
          if(t.id() == ID_struct_tag)
          {
            std::string tag = id2string(to_struct_tag_type(t).get_identifier());
            if(tag.substr(0, 4) == "tag-")
              tag = tag.substr(4);
            pack_subst[sn] = tag;
          }
        }
        if(!pack_subst.empty())
        {
          std::function<void(irept &)> subst = [&](irept &node)
          {
            if(
              node.id() == ID_name &&
              pack_subst.count(id2string(node.get(ID_identifier))))
              node.set(
                ID_identifier,
                pack_subst.at(id2string(node.get(ID_identifier))));
            for(auto &s : node.get_sub())
              subst(s);
            for(auto &ns : node.get_named_sub())
              subst(ns.second);
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          subst(mi);
        }
      }
      // Per [temp.variadic]/7: for non-empty packs, substitute
      // pack parameter names with actual types.
      if(!template_map.pack_args_map.empty() && !new_decl.declarators().empty())
      {
        std::map<std::string, irep_idt> pack_subst;
        for(const auto &pa : template_map.pack_args_map)
        {
          // N5008 [temp.variadic]/5: single-element packs only -- see the
          // guarded mem-init substitution above.
          if(pa.second.size() != 1)
            continue;
          const std::string full = id2string(pa.first);
          auto p = full.rfind("::");
          const std::string sn =
            p != std::string::npos ? full.substr(p + 2) : full;
          const typet &t = pa.second.front();
          if(t.id() == ID_struct_tag)
          {
            // Use the full struct_tag identifier (see comment above).
            pack_subst[sn] = to_struct_tag_type(t).get_identifier();
          }
        }
        if(!pack_subst.empty())
        {
          std::function<void(irept &)> subst = [&](irept &node)
          {
            if(
              node.id() == ID_name &&
              pack_subst.count(id2string(node.get(ID_identifier))))
              node.set(
                ID_identifier,
                pack_subst.at(id2string(node.get(ID_identifier))));
            node.remove(ID_ellipsis);
            for(auto &s : node.get_sub())
              subst(s);
            for(auto &ns : node.get_named_sub())
              subst(ns.second);
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          subst(mi);
        }
      }
    }

    // N5008 [temp.mem.func] + [temp.inst]/2: a member function template of a
    // class template may be defined OUT OF LINE; instantiating it uses that
    // definition.  The in-class declaration carries no body, and the
    // out-of-line definition is recorded only as a `template_methods` entry
    // of the enclosing class template (there is no scope TEMPLATE id for it),
    // so the instance's member-template declarator arrives here with a nil
    // value and the specialization would be silently bodyless ("no body for
    // callee", e.g. std::_Rb_tree::_M_emplace_hint_unique reached from
    // std::map::operator[]).  Attach the raw definition body (and switch to
    // the definition's parameter names, [dcl.fct]/3: the definition's names
    // bind in its body); the deferred method-body drain substitutes the class
    // and method template parameters at conversion, exactly as for a body
    // attached at class-instantiation time.
    if(
      !new_decl.declarators().empty() &&
      new_decl.declarators()[0].value().is_nil())
    {
      const irep_idt member_base_name =
        new_decl.declarators()[0].name().get_base_name();
      bool attached = false;
      for(const auto &tsp : symbol_table)
      {
        if(attached)
          break;
        if(!tsp.second.type.get_bool(ID_is_template))
          continue;
        if(tsp.second.value.is_nil())
          continue;
        const exprt &tms = static_cast<const exprt &>(
          tsp.second.value.find(ID_template_methods));
        for(const auto &tm : tms.operands())
        {
          const cpp_declarationt &md = static_cast<const cpp_declarationt &>(
            static_cast<const irept &>(tm));
          if(md.declarators().empty())
            continue;
          if(md.declarators()[0].name().get_base_name() != member_base_name)
            continue;
          if(md.declarators()[0].find(ID_value).is_nil())
            continue;
          // N5008 [over.load], [dcl.fct]/3: the definition belonging to this
          // member is the one whose SIGNATURE matches; base-name matching
          // alone confuses same-named overloaded member templates (std::
          // pair's two piecewise constructors).  Compare the function
          // parameter count as a cheap faithful discriminator.
          {
            const typet &d_ftype = new_decl.declarators()[0].type();
            const typet &m_ftype = md.declarators()[0].type();
            if(
              d_ftype.id() == ID_function_type &&
              m_ftype.id() == ID_function_type &&
              d_ftype.find(ID_parameters).get_sub().size() !=
                m_ftype.find(ID_parameters).get_sub().size())
              continue;
          }
          // Only adopt from an entry that carries its own template-parameter
          // list (an out-of-line member function template definition always
          // does) and whose OWNING class template matches this member's
          // enclosing class, so a same-named member of an unrelated template
          // is not attached (the known hazard of base-name matching).
          if(md.find(ID_template_type).is_nil())
            continue;
          {
            // template_symbol.name is `<class-instance>::template.<member>...`;
            // the owner id is `[ns::]template.<class><params>`.  Compare the
            // class base names (strip the template-argument/parameter lists).
            const std::string tmpl_name = id2string(template_symbol.name);
            const auto member_sep = tmpl_name.find("::template.");
            std::string class_part = member_sep != std::string::npos
                                       ? tmpl_name.substr(0, member_sep)
                                       : std::string{};
            const auto args_pos = class_part.find('<');
            if(args_pos != std::string::npos)
              class_part.resize(args_pos);
            const auto ns_pos = class_part.rfind("::");
            if(ns_pos != std::string::npos)
              class_part.erase(0, ns_pos + 2);
            std::string owner = id2string(tsp.first);
            const auto tpos = owner.rfind("template.");
            if(tpos != std::string::npos)
              owner.erase(0, tpos + std::string("template.").size());
            const auto owner_args = owner.find('<');
            if(owner_args != std::string::npos)
              owner.resize(owner_args);
            if(class_part.empty() || owner != class_part)
              continue;
          }
          new_decl.declarators()[0].value() =
            static_cast<const exprt &>(md.declarators()[0].find(ID_value));
          // N5008 [class.base.init]/1: the ctor-initializer is part of the
          // constructor's DEFINITION.  An out-of-line delegating constructor
          // (std::pair's piecewise constructor in <tuple>, `: pair(__first,
          // __second, _Build_index_tuple<...>::__type(), ...)`) keeps its
          // mem-initializer-list on the definition's declarator; without
          // copying it the instantiated member converts with NO initializer
          // (members default-initialized, the delegation never happens).
          {
            const irept &m_inits =
              md.declarators()[0].find(ID_member_initializers);
            if(m_inits.is_not_nil())
              new_decl.declarators()[0].member_initializers() = m_inits;
          }
          // Use the definition's parameter names so the body's references
          // bind ([dcl.fct]/3).
          {
            typet &dtype = new_decl.declarators()[0].type();
            const typet &mtype = md.declarators()[0].type();
            if(dtype.id() == ID_function_type && mtype.id() == ID_function_type)
            {
              irept::subt &dparams = dtype.add(ID_parameters).get_sub();
              const irept::subt &mparams = mtype.find(ID_parameters).get_sub();
              for(std::size_t i = 0; i < dparams.size() && i < mparams.size();
                  ++i)
              {
                const irept &mdecl = mparams[i];
                if(
                  dparams[i].id() != ID_cpp_declaration ||
                  mdecl.id() != ID_cpp_declaration)
                  continue;
                const auto &m_declaration =
                  to_cpp_declaration(static_cast<const exprt &>(mdecl));
                auto &d_declaration = static_cast<cpp_declarationt &>(
                  static_cast<irept &>(dparams[i]));
                if(
                  m_declaration.declarators().size() == 1 &&
                  d_declaration.declarators().size() == 1)
                {
                  d_declaration.declarators()[0].name() =
                    m_declaration.declarators()[0].name();
                }
              }
            }
          }
          attached = true;
          break;
        }
      }
    }

    // Per [temp.inst]/3: member function template type-checking
    // may fail when function template parameters are not in the
    // class template map.  Catch and return the template symbol.
    {
      // [temp.spec]/4 + [temp.inst]/2: each specialization of a member
      // function template is a distinct entity.  When the template
      // parameters do not appear in the parameter types, distinct
      // specializations share one function signature and would collide
      // on a single unsuffixed member symbol -- unsound when their
      // values differ (e.g. `template<class U> static unsigned sz()`
      // returning sizeof(U), or std::get<N>).  Mark the instance so
      // typecheck_member_function encodes the instantiation suffix into
      // its symbol name, giving each specialization a distinct symbol.
      // The actual suffixing there is gated on the instance having a
      // body: a member function template whose definition CBMC cannot
      // carry into the instance (e.g. std::_Any_data's reinterpret-cast
      // accessor templates _M_access<T>, whose body does not survive
      // instantiation) must keep its current name so that it merges with
      // -- and reuses the body of -- a non-template overload, which is
      // how it works today.
      new_decl.declarators()[0].set("#member_fn_template_instance", true);
      // [temp.inst]/2 + [temp.deduct]/8: substituting and type-
      // checking a compound member declaration during template
      // instantiation is a SFINAE immediate context — a failure
      // here doesn't invalidate the template specialization, it
      // just means we can't complete this member and bail out to
      // the caller with the template symbol.
      // N5008 [temp.variadic]/7: when this member function template's own
      // trailing parameter pack deduced EMPTY (argument list shorter than
      // the parameter list, or the `empty_typet` zero-elements sentinel at
      // the pack's position), the pack parameter expands to nothing and
      // every expansion referencing it -- including in the TRAILING RETURN
      // TYPE's decltype -- yields zero call arguments.  Strip both before
      // type-checking; otherwise the decltype resolves against a dead name
      // (`symbol 'args' is unknown`, libc++ __perfect_forward's
      // `operator()(_Args&&... __args) -> decltype(_Op()(..., __args...))`
      // invoked with no arguments) and the member is dropped.
      {
        const auto &mtps = template_type.template_parameters();
        const bool m_trailing_pack =
          !mtps.empty() && mtps.back().get_bool(ID_ellipsis);
        const bool m_short_args =
          full_template_args.arguments().size() < mtps.size();
        const bool m_sentinel =
          full_template_args.arguments().size() == mtps.size() &&
          !full_template_args.arguments().empty() &&
          full_template_args.arguments().back().id() == ID_type &&
          full_template_args.arguments().back().type().id() == ID_empty;
        if(m_trailing_pack && (m_short_args || m_sentinel))
        {
          // the EMPTY template pack's short name (e.g. `Args`)
          std::string m_pack_short;
          {
            const std::string mf =
              id2string(mtps.back().type().get(ID_identifier));
            const auto mp = mf.rfind("::");
            m_pack_short = mp != std::string::npos ? mf.substr(mp + 2) : mf;
          }
          // the pack parameter's name (e.g. `args` in `Args... args`).
          // N5008 [dcl.fct]/6: `B...` where B is NOT a pack is B followed
          // by C varargs, not a pack declarator -- only remove a parameter
          // whose type names THE empty pack (own-pack match, mirroring the
          // constructor-template removal above); removing a varargs
          // parameter dropped `operator()(F, B...)` overloads whenever an
          // unrelated trailing template pack deduced empty.
          irep_idt m_pack_var;
          typet &fdt = new_decl.declarators()[0].type();
          if(fdt.id() == ID_function_type)
          {
            irept &fps = fdt.add(ID_parameters);
            auto &fsub = fps.get_sub();
            for(auto it = fsub.begin(); it != fsub.end(); ++it)
            {
              if(it->id() != ID_cpp_declaration)
                continue;
              const auto &fpd = static_cast<const cpp_declarationt &>(*it);
              if(
                fpd.declarators().empty() ||
                (!fpd.declarators().front().get_bool(ID_ellipsis) &&
                 !fpd.declarators().front().type().get_bool(ID_ellipsis) &&
                 !fpd.type().get_bool(ID_ellipsis)))
                continue;
              const irept *t = &static_cast<const irept &>(fpd.type());
              while(t->id() != ID_cpp_name && !t->get_sub().empty())
                t = &t->get_sub().front();
              std::string own;
              if(t->id() == ID_cpp_name && !t->get_sub().empty())
                own = id2string(t->get_sub().front().get(ID_identifier));
              if(own != m_pack_short)
                continue;
              for(const auto &nsub : fpd.declarators().front().name().get_sub())
                if(nsub.id() == ID_name)
                  m_pack_var = nsub.get(ID_identifier);
              fsub.erase(it);
              break;
            }
          }
          // The parameter may already have been removed by the earlier
          // substitution; recover the pack parameter's NAME from the
          // original template declaration (mirroring the recovery in the
          // constructor-template expansion below).
          if(
            m_pack_var.empty() &&
            template_symbol.type.id() == ID_cpp_declaration)
          {
            const cpp_declarationt &m_orig =
              to_cpp_declaration(template_symbol.type);
            if(!m_orig.declarators().empty())
            {
              const typet &modt = m_orig.declarators().front().type();
              if(modt.id() == ID_function_type)
              {
                for(const auto &opi : modt.find(ID_parameters).get_sub())
                {
                  if(opi.id() != ID_cpp_declaration)
                    continue;
                  const auto &opd = static_cast<const cpp_declarationt &>(opi);
                  if(
                    opd.declarators().empty() ||
                    (!opd.declarators().front().get_bool(ID_ellipsis) &&
                     !opd.declarators().front().type().get_bool(ID_ellipsis) &&
                     !opd.type().get_bool(ID_ellipsis)))
                    continue;
                  // own-pack match only ([dcl.fct]/6: `B...` with B a
                  // non-pack is C varargs, not this pack's declarator)
                  const irept *ot = &static_cast<const irept &>(opd.type());
                  while(ot->id() != ID_cpp_name && !ot->get_sub().empty())
                    ot = &ot->get_sub().front();
                  std::string oown;
                  if(ot->id() == ID_cpp_name && !ot->get_sub().empty())
                    oown = id2string(ot->get_sub().front().get(ID_identifier));
                  if(oown != m_pack_short)
                    continue;
                  for(const auto &nsub :
                      opd.declarators().front().name().get_sub())
                    if(nsub.id() == ID_name)
                      m_pack_var = nsub.get(ID_identifier);
                }
              }
            }
          }
          if(!m_pack_var.empty())
          {
            std::function<bool(const irept &)> m_refs =
              [&](const irept &n) -> bool
            {
              if(n.id() == ID_cpp_name)
                for(const auto &sn : n.get_sub())
                  if(sn.id() == ID_name && sn.get(ID_identifier) == m_pack_var)
                    return true;
              for(const auto &sn : n.get_sub())
                if(m_refs(sn))
                  return true;
              for(const auto &ns : n.get_named_sub())
                if(m_refs(ns.second))
                  return true;
              return false;
            };
            std::function<void(irept &)> m_strip = [&](irept &node)
            {
              if(
                node.id() == ID_side_effect &&
                node.get(ID_statement) == ID_function_call)
              {
                for(auto &sub : node.get_sub())
                  if(sub.id() == ID_arguments)
                  {
                    auto &asub = sub.get_sub();
                    asub.erase(
                      std::remove_if(
                        asub.begin(),
                        asub.end(),
                        [&](const irept &a) {
                          return (a.id() == ID_cpp_name ||
                                  a.get_bool(ID_ellipsis)) &&
                                 m_refs(a);
                        }),
                      asub.end());
                  }
              }
              for(auto &sub : node.get_sub())
                m_strip(sub);
              for(auto &ns : node.get_named_sub())
                m_strip(ns.second);
            };
            m_strip(new_decl.declarators()[0].type());
            // the trailing-return decltype may live in the DECLARATION's
            // type (the decl-specifier seq), not the declarator's
            m_strip(new_decl.type());
            if(new_decl.declarators()[0].value().is_not_nil())
              m_strip(new_decl.declarators()[0].value());
          }
        }
      }
      try
      {
        sfinae_contextt sfinae_guard{*this};
        typecheck_compound_declarator(
          symb,
          new_decl,
          new_decl.declarators()[0],
          to_struct_union_type(symb.type).components(),
          access,
          is_static,
          false,
          false);
      }
      catch(...)
      {
        return template_symbol;
      }
    }

    const symbolt &method_sym =
      lookup(to_struct_union_type(symb.type).components().back().get_name());

    // Condition-3 detection: a same-signature non-template overload occupying
    // the unsuffixed name that this suffixed member function template
    // specialization shadows.  Checked here -- after typecheck_compound_-
    // declarator, with the enclosing class fully elaborated -- so the overload
    // (if any) is reliably present, unlike at the earlier naming point.
    const irep_idt unsuffixed_name =
      to_struct_union_type(symb.type).components().back().get(
        "#unsuffixed_name");
    const bool is_cond3 =
      !unsuffixed_name.empty() && symbol_table.has_symbol(unsuffixed_name);

    // The method was added to deferred_typechecking by
    // typecheck_compound_declarator (because the parent scope is a template
    // scope). Since we are actually instantiating this method, move it
    // from deferred_typechecking to method_bodies so the body gets
    // type-checked and is not erased during clean_up.
    if(deferred_typechecking.erase(method_sym.name))
    {
      symbolt &ws = symbol_table.get_writeable_ref(method_sym.name);
      // Per [temp.inst]/1: store function template parameters and
      // arguments so method_bodies can restore the template_map.
      ws.type.add(irep_idt{"#fn_template_type"}) = template_type;
      ws.type.add(irep_idt{"#fn_template_args"}) = specialization_template_args;
      // N5008 [temp.variadic]/5,8: with MULTIPLE parameter packs (std::pair's
      // piecewise delegation target `template<class... _Args1,
      // size_t... _Indexes1, class... _Args2, size_t... _Indexes2>`), the
      // flat #fn_template_args list cannot encode how the arguments split
      // between the packs; the drain's template-map rebuild would misbind
      // them and the body would fail to convert (silently dropped for a
      // system header).  Persist the deduction-time pack bindings -- TYPE
      // pack elements from pack_args_map, NON-TYPE pack values from
      // pack_expr_map -- for prepare_deferred_method_body to replay.
      {
        std::size_t n_packs = 0;
        for(const auto &tp : template_type.template_parameters())
          if(tp.get_bool(ID_ellipsis))
            ++n_packs;
        if(n_packs > 1)
        {
          irept packs("deduced_packs");
          for(const auto &tp : template_type.template_parameters())
          {
            if(!tp.get_bool(ID_ellipsis))
              continue;
            const irep_idt pid = tp.id() == ID_type
                                   ? tp.type().get(ID_identifier)
                                   : tp.get(ID_identifier);
            irept entry(tp.id() == ID_type ? ID_type : ID_expression);
            entry.set(ID_identifier, pid);
            if(tp.id() == ID_type)
            {
              const auto pa_it = template_map.pack_args_map.find(pid);
              if(pa_it != template_map.pack_args_map.end())
                for(const auto &t : pa_it->second)
                  entry.get_sub().push_back(t);
            }
            else
            {
              const auto pe_it = template_map.pack_expr_map.find(pid);
              if(pe_it != template_map.pack_expr_map.end())
                for(const auto &v : pe_it->second)
                  entry.get_sub().push_back(v);
            }
            packs.get_sub().push_back(entry);
          }
          ws.type.add(irep_idt{"#fn_template_packs"}) = packs;
        }
      }

      // [temp.inst]/5: a function template specialization is implicitly
      // instantiated -- including its definition -- when referenced in a
      // context that requires the definition to exist, such as a constant
      // expression ([expr.const]).  A `constexpr` member function template
      // specialization may be folded during the enclosing type-check (e.g.
      // as a template argument `S<TC::f<int>()>`, or in the SFINAE
      // constraints of std::tuple's constructors), which happens before
      // the deferred method-body pass (typecheck_method_bodies) runs.
      // A condition-3 specialization (one shadowing a same-signature
      // non-template overload) is also converted eagerly so we can tell
      // whether its definition survives instantiation and decide between a
      // distinct symbol and the overload fallback below.
      // Type-check its body eagerly now, using the function template map
      // currently in effect, mirroring the eager conversion of free
      // function template specializations (convert_non_template_declaration
      // below).  On failure (e.g. an unused, ill-formed specialization in a
      // SFINAE context) restore the error count and fall back to the normal
      // deferred path so that overload resolution can proceed.
      //
      // N5008 [temp.inst]/5, [expr.const]: eager instantiation is required
      // only when the specialization must yield a *constant* now (a template
      // argument, an array bound, a foldable `::value`, ...).  A constexpr
      // function whose return type is `void` never produces such a value, so
      // it never needs eager folding; converting it eagerly here -- nested in
      // the referencing body's degraded, suppression-active context, and
      // before the deferred body-pack expander runs -- is pure downside.  In
      // particular a void constexpr member function template wrapping
      // std::construct_at (the C++20 allocator_traits::construct shape) has a
      // function-parameter-pack new-initializer expansion that only the
      // deferred prepare_deferred_method_body pass expands; forcing it eager
      // resolves the still-packed call and drops the body.  Defer such
      // functions to the drain, exactly as for a non-constexpr member.
      const bool eager_returns_void =
        ws.type.id() == ID_code &&
        to_code_type(ws.type).return_type().id() == ID_empty;
      if(
        (new_decl.storage_spec().is_constexpr() && !eager_returns_void) ||
        is_cond3)
      {
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        // Pristine copy of the parsed body, restored if the eager conversion
        // below throws mid-way (see the catch).
        const exprt saved_body = ws.value;
        // [temp.variadic]/5: if this member function template belongs to a
        // class template instantiation, its body may expand the *class*
        // parameter pack alongside its own (e.g. the constexpr tuple-
        // constructor constraints `__and_<is_constructible<_Types,
        // _UTypes>...>::value`).  Bring the class's template arguments into
        // the active template map -- as the deferred method-body pass does
        // via add_method_body -- so that such a zipped multi-pack expansion
        // resolves both packs; otherwise the class pack stays unbound, the
        // expansion is left unexpanded, and the constexpr call cannot be
        // folded.  build() merges, preserving this function's own pack.
        // N5008 [temp.point]/1: the eager conversion's template-map
        // modifications (class-pack binding, forcing not-yet-bound packs to
        // size 0) must not leak into the deferred-drain requeue below --
        // add_method_body snapshots the CURRENT template_map, and a leaked
        // "pack forced empty" entry makes the drain replay a broken map so
        // the body's genuine (non-empty) pack expansion is dropped.  Confine
        // the eager map to an inner scope and requeue only after it is
        // restored.
        bool eager_ok = false;
        {
          cpp_saved_template_mapt saved_eager_map(template_map);
          {
            const irep_idt &member_class = ws.type.get(ID_C_member_name);
            if(!member_class.empty())
            {
              const symbolt *class_sym = symbol_table.lookup(member_class);
              if(
                class_sym != nullptr &&
                class_sym->type.find(ID_C_template).is_not_nil() &&
                class_sym->type.find(ID_C_template_arguments).is_not_nil())
              {
                template_map.build(
                  static_cast<const template_typet &>(
                    class_sym->type.find(ID_C_template)),
                  static_cast<const cpp_template_args_tct &>(
                    class_sym->type.find(ID_C_template_arguments)));
              }
            }
          }
          // N5008 [temp.variadic]/7: a member function template instantiated
          // with an empty type pack (e.g. std::tuple's
          // `__is_constructible<>()`) has zero-length pack expansions in its
          // body.  Record the empty packs and collapse those expansions
          // (`Tr<U...>` -> `Tr<>`) before the eager conversion, so the body's
          // `cpp_name`s resolve here instead of being left un-typechecked and
          // falling back to the deferred path (which cannot resolve them,
          // making the constexpr body fold to a wrong value).
          for(const auto &p : template_type.template_parameters())
          {
            if(!p.get_bool(ID_ellipsis))
              continue;
            const irep_idt pid = p.type().get(ID_identifier);
            if(
              !pid.empty() &&
              template_map.type_map.find(pid) == template_map.type_map.end() &&
              template_map.pack_args_map.find(pid) ==
                template_map.pack_args_map.end())
              template_map.pack_size_map[pid] = 0;
          }
          if(ws.value.is_not_nil())
            remove_empty_pack_expansion_args(ws.value);
          // N5008 [temp.variadic]/5: expand pack-expansion
          // mem-initializers before the eager conversion (the deferred
          // drain does this in prepare_deferred_method_body; this
          // eager path previously left the ellipsis and raw pack names
          // behind, so std::pair's piecewise target constructor failed
          // to convert and was silently dropped).
          if(ws.value.is_not_nil())
            expand_member_initializer_packs_in_body(
              static_cast<irept &>(ws.value),
              template_map.pack_args_map,
              template_map.pack_expr_map);
          // STANDARD GAP (N5008 [temp.point]/1, [temp.inst]/5): this eagerly
          // converts a *constexpr* member function-template specialization's
          // *definition* inline, nested in the referencing body's conversion,
          // rather than at the enclosing namespace-scope point of instantiation
          // (the deferred `typecheck_method_bodies` drain reached via
          // `add_method_body`, used in the `else` branch below).  The eager
          // conversion exists because a constexpr specialization used as a
          // constant (e.g. an `enable_if` non-type argument, or std::tuple's
          // constructor SFINAE) must be *foldable now*; but doing the full body
          // conversion in this nested, suppression-active context is a source of
          // the degradation documented in doc/architectural/cpp-frontend-review-
          // 2026-06-23-instantiation-context.md.  The correct split is to fold
          // the constant eagerly while deferring the runtime (GOTO) definition to
          // the queue; on failure we already fall back to `add_method_body`.
          try
          {
            convert_function(ws);
            // Prevent the deferred pass from converting it a second time.
            methods_seen.insert(ws.name);
            eager_ok = true;
          }
          catch(...)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            // The eager conversion mutates ws.value in place (typecheck_code)
            // and may throw partway; restore the pristine parsed body so the
            // deferred drain re-type-checks from it (its
            // prepare_deferred_method_body pack-expander then handles a
            // std::construct_at-style new-initializer pack expansion in a
            // constexpr allocator_traits::construct wrapper).
            ws.value = saved_body;
          }
        }
        if(!eager_ok)
          add_method_body(&ws);
      }
      else
        add_method_body(&ws);
    }

    // [temp.spec]/4 condition-3 fallback: a member function template
    // specialization that shadows a same-signature non-template overload and
    // whose own definition did not survive instantiation (no body -- e.g.
    // std::_Any_data::_M_access<T>, whose reinterpret-cast body is dropped)
    // cannot be a usable distinct entity.  Resolve calls to the non-template
    // overload instead, reproducing the same-signature merge that makes such
    // accessors work; the bodyless suffixed symbol is left unreferenced and
    // removed during clean-up.  This is checked outside the
    // deferred_typechecking branch above because a specialization may be
    // instantiated more than once and the first (call-binding) request can be
    // the one that is not pending deferred type-checking.  A specialization
    // whose body *did* survive (e.g. a value-dependent `f<int>()` alongside a
    // non-template `f()`) keeps its distinct symbol.
    if(is_cond3)
    {
      const symbolt *ms = symbol_table.lookup(method_sym.name);
      if(ms != nullptr && ms->value.is_nil())
      {
        const symbolt *overload_sym = symbol_table.lookup(unsuffixed_name);
        if(overload_sym != nullptr)
          return *overload_sym;
      }
    }

    return method_sym;
  }

  // not a class template, not a class template method,
  // it must be a function template, a template alias, or a variable template!

  if(new_decl.declarators().size() != 1)
  {
    error().source_location = source_location;
    error() << "expected exactly one declarator in template" << eom;
    throw 0;
  }

  // Variable template: the declarator type is not a function type.
  // Instantiate by converting the declaration directly.
  if(
    !new_decl.declarators().empty() &&
    new_decl.declarators()[0].type().id() != ID_function_type &&
    new_decl.type().id() != ID_struct && new_decl.type().id() != ID_union &&
    !new_decl.is_typedef())
  {
    // Check for a better-matching partial specialization.
    if(template_symbol.type.get(ID_specialization_of).empty())
    {
      // Resolve symbol references in full_template_args so that
      // expressions like "x % y" (where x, y are const symbols)
      // are simplified to constants for matching.
      cpp_template_args_tct full_args_resolved = full_template_args;
      for(auto &arg : full_args_resolved.arguments())
      {
        if(arg.id() == ID_type)
          continue;
        for(int pass = 0; pass < 10; ++pass)
        {
          bool changed = false;
          arg.visit_pre(
            [this, &changed](exprt &node)
            {
              if(node.id() == ID_symbol)
              {
                const symbolt &sym =
                  lookup(to_symbol_expr(node).get_identifier());
                if(sym.value.is_not_nil() && cpp_is_pod(sym.type))
                {
                  node = sym.value;
                  changed = true;
                }
              }
            });
          if(!changed)
            break;
          simplify(arg, *this);
          if(arg.is_constant())
            break;
        }
      }

      cpp_scopet *ts = id_map_lookup(cpp_scopes, template_symbol.name);
      if(ts != nullptr)
      {
        cpp_scopet &parent_scope = ts->get_parent();
        cpp_scopet::id_sett id_set = parent_scope.lookup(
          template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

        const symbolt *best_match = nullptr;
        cpp_template_args_tct best_spec_args;

        // [temp.deduct]/8 + [temp.class.spec.match]: specialization
        // matching for the second search (after primary-template
        // substitution of explicit args).
        sfinae_contextt spec_sfinae_guard{*this};

        for(const auto *id_ptr : id_set)
        {
          const symbolt &s = lookup(id_ptr->identifier);
          if(s.type.get(ID_specialization_of).empty())
            continue;

          const cpp_declarationt &spec_decl = to_cpp_declaration(s.type);
          const cpp_template_args_non_tct &partial_args =
            spec_decl.partial_specialization_args();

          if(
            partial_args.arguments().size() !=
            full_args_resolved.arguments().size())
            continue;

          cpp_saved_template_mapt saved_map2(template_map);
          cpp_save_scopet save_scope2(cpp_scopes);

          template_map.build_unassigned(spec_decl.template_type());

          cpp_scopet *spec_scope = id_map_lookup(cpp_scopes, s.name);
          if(spec_scope != nullptr)
            cpp_scopes.go_to(*spec_scope);

          cpp_typecheck_resolvet resolver(*this);
          // [temp.deduct.type]/8: partial-specialization matching
          // rejects cv-mismatched patterns (see the flag's doc in
          // cpp_typecheck_resolve.h).
          resolver.strict_cv_deduction = true;

          for(std::size_t i = 0; i < full_args_resolved.arguments().size(); i++)
          {
            if(full_args_resolved.arguments()[i].id() == ID_type)
              resolver.guess_template_args(
                partial_args.arguments()[i].type(),
                full_args_resolved.arguments()[i].type());
            else
              resolver.guess_template_args(
                partial_args.arguments()[i], full_args_resolved.arguments()[i]);
          }

          cpp_template_args_tct guessed =
            template_map.build_template_args(spec_decl.template_type());

          if(guessed.has_unassigned() || guessed.has_conflict())
            continue;

          // N5008 [temp.variadic]/5: build_template_args emits a single
          // scalar placeholder per template parameter PACK (the pack's first
          // element).  For the actual instantiation the pack must be expanded
          // to one argument per deduced element -- otherwise e.g. the `E` of a
          // variable-template partial specialization
          // `tsize_v<tup<E...>> = sizeof...(E)` (libstdc++'s
          // tuple_size_v<tuple<_Types...>>) collapses to one element and
          // sizeof...(E) evaluates to 1.  Mirrors the class partial-spec
          // expansion in disambiguate_template_classes.
          {
            const auto &spec_params =
              spec_decl.template_type().template_parameters();
            cpp_template_args_tct::argumentst expanded_args;
            for(std::size_t i = 0; i < guessed.arguments().size(); i++)
            {
              if(i < spec_params.size() && spec_params[i].get_bool(ID_ellipsis))
              {
                const irep_idt pid =
                  spec_params[i].id() == ID_type
                    ? spec_params[i].type().get(ID_identifier)
                    : spec_params[i].get(ID_identifier);
                const auto pa_it = template_map.pack_args_map.find(pid);
                if(pa_it != template_map.pack_args_map.end())
                {
                  for(const auto &pt : pa_it->second)
                    expanded_args.push_back(exprt(ID_type, pt));
                  continue;
                }
                const auto pe_it = template_map.pack_expr_map.find(pid);
                if(pe_it != template_map.pack_expr_map.end())
                {
                  for(const auto &pv : pe_it->second)
                    expanded_args.push_back(pv);
                  continue;
                }
              }
              expanded_args.push_back(guessed.arguments()[i]);
            }
            guessed.arguments().swap(expanded_args);
          }

          cpp_template_args_tct partial_tc;
          bool sfinae_failed = false;
          {
            // [temp.deduct]/8: substituting explicit template args
            // into the partial specialization's parameter list may
            // fail; treat as SFINAE and skip this candidate.
            sfinae_contextt sfinae_guard{*this};
            try
            {
              partial_tc = typecheck_template_args(
                source_location, template_symbol, partial_args);
            }
            catch(...)
            {
              sfinae_failed = true;
            }
          }
          if(sfinae_failed)
            continue;

          if(partial_tc == full_args_resolved)
          {
            // Also check #c_type to distinguish e.g. char from
            // signed char.
            bool c_type_match = true;
            for(std::size_t j = 0; j < partial_tc.arguments().size(); j++)
            {
              const exprt &p = partial_tc.arguments()[j];
              const exprt &f = full_args_resolved.arguments()[j];
              if(
                p.id() == ID_type &&
                p.type().get(ID_C_c_type) != f.type().get(ID_C_c_type))
              {
                c_type_match = false;
                break;
              }
            }
            if(!c_type_match)
              continue;

            // Evaluate concept constraints on template parameters.
            // Skip specializations whose concept is not satisfied.
            {
              const auto &spec_params =
                spec_decl.template_type().template_parameters();
              bool concept_ok = true;
              for(std::size_t pi = 0;
                  pi < spec_params.size() &&
                  pi < full_args_resolved.arguments().size();
                  ++pi)
              {
                const irep_idt &cc =
                  spec_params[pi].get("#C_concept_constraint");
                if(cc.empty())
                  continue;
                const auto concept_ids =
                  cpp_scopes.current_scope().lookup(cc, cpp_scopet::RECURSIVE);
                if(concept_ids.empty())
                  continue;
                const auto *concept_sym =
                  symbol_table.lookup((*concept_ids.begin())->identifier);
                if(!concept_sym || !concept_sym->type.get_bool(ID_is_template))
                  continue;
                const cpp_declarationt &concept_decl =
                  to_cpp_declaration(concept_sym->type);
                if(concept_decl.declarators().empty())
                  continue;
                exprt body = concept_decl.declarators()[0].value();
                if(body.is_nil())
                  continue;
                template_mapt cmap;
                cpp_template_args_tct cargs;
                cargs.arguments().push_back(full_args_resolved.arguments()[pi]);
                cmap.build(concept_decl.template_type(), cargs);
                cmap.apply(body);
                // [temp.constr.constr] + [temp.deduct]/8: concept
                // body evaluation is SFINAE-guarded; failure to
                // substitute or a `false` result means the concept
                // is not satisfied, not an ill-formed program.
                bool old_suppress = suppress_elaborate;
                suppress_elaborate = false;
                try
                {
                  sfinae_contextt sfinae_guard{*this};
                  typecheck_expr(body);
                  simplify(body, *this);
                  if(body.is_false())
                    concept_ok = false;
                }
                catch(...)
                {
                  concept_ok = false;
                }
                suppress_elaborate = old_suppress;
                if(!concept_ok)
                  break;
              }
              if(!concept_ok)
                continue;
            }

            best_match = &s;
            best_spec_args = guessed;
          }
        }

        if(best_match != nullptr)
        {
          return instantiate_template(
            source_location, *best_match, best_spec_args, full_args_resolved);
        }
      }
    }

    // Append template suffix to the declarator name
    {
      cpp_namet &declarator_name = new_decl.declarators()[0].name();
      for(auto &sub : declarator_name.get_sub())
      {
        if(sub.id() == ID_name)
        {
          sub.set(ID_identifier, id2string(sub.get(ID_identifier)) + suffix);
          break;
        }
      }
    }

    // Force elaboration during variable template body processing
    // so that nested type traits (e.g., is_nothrow_destructible<T>::value)
    // can be fully resolved.
    {
      // C++20 [expr.prim.req.general]/2 and /4: if this variable template is a
      // concept one of whose constraint-expressions is a requires-expression,
      // bind that requires-expression's requirement-parameter-list as local
      // symbols in the current (instantiation) scope so the requirement
      // sub-expressions that mention them resolve.  Without this, a concept
      // like `requires(T a){ a + a; }` fails with `symbol 'a' is unknown` when
      // its concept-id is evaluated as a value.  The parameters are notation
      // only (no linkage/lifetime), so the marker is removed after binding.
      //
      // A requires-expression may be only a *conjunct* of a larger
      // constraint-expression (e.g. `same_as<T,T> && requires(T a){...}`), in
      // which case its `#requires_params` sits on an inner node rather than the
      // top-level value.  Bind the parameters of every requires-expression in
      // the body, not just one at the top, so conjoined requires-expressions
      // (as in std::assignable_from, std::swappable, ...) resolve their
      // parameters too.
      exprt &init = new_decl.declarators()[0].value();
      const auto bind_requires_params = [&](exprt &node)
      {
        const irept &req_params = node.find("#requires_params");
        if(req_params.is_nil() || req_params.get_sub().empty())
          return;
        for(const auto &param : req_params.get_sub())
        {
          const irep_idt pname = param.get(ID_name);
          if(pname.empty())
            continue;
          typet ptype = static_cast<const typet &>(param.find(ID_type));
          template_map.apply(ptype);
          try
          {
            sfinae_contextt sfinae_guard{*this};
            typecheck_type(ptype);
          }
          catch(...)
          {
          }
          const irep_idt id = "requires_param::" + id2string(pname);
          if(!symbol_table.has_symbol(id))
          {
            symbolt param_sym{id, ptype, ID_cpp};
            param_sym.base_name = pname;
            param_sym.is_lvalue = true;
            symbol_table.add(param_sym);
          }
          else
            symbol_table.get_writeable_ref(id).type = ptype;
          cpp_idt &scope_id = cpp_scopes.current_scope().insert(pname);
          scope_id.identifier = id;
          scope_id.id_class = cpp_idt::id_classt::SYMBOL;
        }
        node.remove("#requires_params");
      };
      // Top-level requires-expression (whole concept body), then any
      // requires-expressions nested as conjuncts of the constraint-expression.
      bind_requires_params(init);
      init.visit_pre(bind_requires_params);

      bool old_suppress = suppress_elaborate;
      suppress_elaborate = false;
      convert_non_template_declaration(new_decl);
      suppress_elaborate = old_suppress;
    }

    const symbolt &symb = lookup(new_decl.declarators()[0].get(ID_identifier));

    return symb;
  }

  // For template aliases (typedefs) and function templates where different
  // template arguments may produce the same parameter types (e.g., when a
  // template parameter only affects the return type), append the template
  // suffix to the declarator name so that different instantiations produce
  // different symbols.
  {
    cpp_namet &declarator_name = new_decl.declarators()[0].name();
    for(auto &sub : declarator_name.get_sub())
    {
      if(sub.id() == ID_name)
      {
        sub.set(ID_identifier, id2string(sub.get(ID_identifier)) + suffix);
        break;
      }
    }
  }

  // When a variadic template parameter pack has zero arguments (the args
  // list is shorter than the parameter list, OR the pack's position holds
  // the `empty_typet` zero-elements sentinel -- both encodings reach this
  // point; see template_map.cpp's single-pack binding), remove
  // pack-expanded parameters from the function declaration and its nested
  // types.  N5008 [temp.variadic]/7.
  const bool trailing_pack_is_empty_sentinel =
    !template_type.template_parameters().empty() &&
    template_type.template_parameters().back().get_bool(ID_ellipsis) &&
    full_template_args.arguments().size() ==
      template_type.template_parameters().size() &&
    !full_template_args.arguments().empty() &&
    full_template_args.arguments().back().id() == ID_type &&
    full_template_args.arguments().back().type().id() == ID_empty;
  if(
    (full_template_args.arguments().size() <
       template_type.template_parameters().size() ||
     trailing_pack_is_empty_sentinel) &&
    !template_type.template_parameters().empty() &&
    template_type.template_parameters().back().get_bool(ID_ellipsis))
  {
    // Get the pack parameter's short name
    const auto &pack_param = template_type.template_parameters().back();
    const std::string full_id = id2string(pack_param.type().get(ID_identifier));
    auto pos = full_id.rfind("::");
    const std::string pack_name =
      pos != std::string::npos ? full_id.substr(pos + 2) : full_id;

    // Helper: check if a parameter references the pack
    auto refs_pack = [&pack_name](const irept &p) -> bool
    {
      if(p.id() == ID_ellipsis)
        return true;
      if(p.id() == ID_cpp_declaration)
      {
        const auto &d = to_cpp_declaration(p);
        if(
          !d.declarators().empty() &&
          d.declarators().front().type().get_bool(ID_ellipsis))
          return true;
        if(d.type().id() == ID_cpp_name)
        {
          for(const auto &sub : d.type().get_sub())
          {
            if(
              sub.id() == ID_name &&
              id2string(sub.get(ID_identifier)) == pack_name)
              return true;
          }
        }
      }
      return false;
    };

    // Strip from the function's own parameters
    auto &func_decl = new_decl.declarators()[0];
    irept &func_params = func_decl.type().add(ID_parameters);
    irept::subt &fp_sub = func_params.get_sub();

    // Get the pack variable name before removing (e.g. "base" from
    // "Base... base")
    irep_idt pack_var_name;
    for(const auto &fp : fp_sub)
    {
      if(fp.id() == ID_cpp_declaration)
      {
        const auto &d = to_cpp_declaration(fp);
        if(
          !d.declarators().empty() &&
          d.declarators().front().type().get_bool(ID_ellipsis))
        {
          const auto &dname = d.declarators().front().name();
          for(const auto &sub : dname.get_sub())
          {
            if(sub.id() == ID_name)
            {
              pack_var_name = sub.get(ID_identifier);
              break;
            }
          }
          break;
        }
      }
    }

    fp_sub.erase(
      std::remove_if(fp_sub.begin(), fp_sub.end(), refs_pack), fp_sub.end());

    // Strip from nested function pointer parameter types
    for(auto &fp : fp_sub)
    {
      if(fp.id() == ID_cpp_declaration)
      {
        auto &inner_decl = to_cpp_declaration(fp);
        if(!inner_decl.declarators().empty())
        {
          irept &dtype = inner_decl.declarators().front().type();
          if(
            dtype.id() == ID_frontend_pointer && !dtype.get_sub().empty() &&
            dtype.get_sub().front().id() == ID_function_type)
          {
            irept::subt &inner_params =
              dtype.get_sub().front().add(ID_parameters).get_sub();
            inner_params.erase(
              std::remove_if(
                inner_params.begin(), inner_params.end(), refs_pack),
              inner_params.end());
          }
        }
      }
    }
    // The function parameter pack may already have been removed from the
    // instantiated declaration (e.g. by parameter-pack expansion during
    // substitution).  Recover its name from the original template so the body
    // expansion below can still strip its (now empty) call-argument
    // references.
    if(pack_var_name.empty() && template_symbol.type.id() == ID_cpp_declaration)
    {
      const cpp_declarationt &orig_decl =
        to_cpp_declaration(template_symbol.type);
      if(!orig_decl.declarators().empty())
      {
        const typet &odt = orig_decl.declarators().front().type();
        if(odt.id() == ID_function_type)
        {
          for(const auto &op : odt.find(ID_parameters).get_sub())
          {
            if(op.id() != ID_cpp_declaration)
              continue;
            const auto &od = to_cpp_declaration(op);
            if(
              !od.declarators().empty() &&
              od.declarators().front().type().get_bool(ID_ellipsis))
            {
              for(const auto &s : od.declarators().front().name().get_sub())
                if(s.id() == ID_name)
                {
                  pack_var_name = s.get(ID_identifier);
                  break;
                }
            }
          }
        }
      }
    }
    // Strip pack variable references from function call arguments in the
    // body AND in the declarator's type: a trailing return type may spell
    // the same empty expansion, e.g. libc++ __perfect_forward's
    // `auto operator()(_Args&&... __args) const
    //    -> decltype(_Op()(..., __args...))` instantiated with an EMPTY
    // _Args ([temp.variadic]/5: the expansion yields zero arguments; the
    // reference must vanish with it, or the instantiated return type names
    // an unknown symbol and the member is dropped).
    if(!pack_var_name.empty())
    {
      // Recursively remove pack variable from function call arguments
      std::function<void(irept &)> strip_pack_var;
      strip_pack_var = [&pack_var_name, &strip_pack_var](irept &node)
      {
        // If this is a function_call side_effect, strip pack var from args
        if(
          node.id() == ID_side_effect &&
          node.get(ID_statement) == ID_function_call)
        {
          // Arguments are stored as a positional sub-node with id=arguments
          for(auto &sub : node.get_sub())
          {
            if(sub.id() == ID_arguments)
            {
              irept::subt &arg_sub = sub.get_sub();
              arg_sub.erase(
                std::remove_if(
                  arg_sub.begin(),
                  arg_sub.end(),
                  [&pack_var_name](const irept &a)
                  {
                    // N5008 [temp.variadic]/5: an empty pack expansion yields
                    // zero arguments.  Drop both a bare value-pack argument
                    // (`a`) and a pattern argument that is a pack expansion
                    // referencing the pack (e.g. `static_cast<A&&>(a)...`,
                    // marked with ID_ellipsis), so `f(static_cast<A&&>(a)...)`
                    // with an empty pack becomes `f()`.
                    std::function<bool(const irept &)> refs_pack =
                      [&](const irept &n) -> bool
                    {
                      if(n.id() == ID_cpp_name)
                        for(const auto &s : n.get_sub())
                          if(
                            s.id() == ID_name &&
                            s.get(ID_identifier) == pack_var_name)
                            return true;
                      for(const auto &s : n.get_sub())
                        if(refs_pack(s))
                          return true;
                      for(const auto &ns : n.get_named_sub())
                        if(refs_pack(ns.second))
                          return true;
                      return false;
                    };
                    const bool bare = a.id() == ID_cpp_name && refs_pack(a);
                    return bare || (a.get_bool(ID_ellipsis) && refs_pack(a));
                  }),
                arg_sub.end());
              break;
            }
          }
        }
        // Recurse into sub-nodes
        for(auto &sub : node.get_sub())
          strip_pack_var(sub);
        // Also recurse into named sub-nodes
        for(auto &named : node.get_named_sub())
          strip_pack_var(named.second);
      };
      if(func_decl.value().is_not_nil())
        strip_pack_var(func_decl.value());
      strip_pack_var(func_decl.type());
    }
  }

  // [temp.variadic]/5 + [temp.param]/11: expand the function parameter pack
  // into its N elements and expand pack references in the function body.  N is
  // the number of pack arguments excluding the empty-pack sentinel (an
  // `ID_type` argument whose type is `ID_empty`, used to encode a pack that
  // matched zero elements).  N >= 2 expands into individual parameters; N == 0
  // removes the pack parameter and its body call-argument references; N == 1
  // needs no expansion here (the single element already maps to the single
  // parameter).
  //
  // The template parameter pack need NOT be the last template parameter: a pack
  // may be followed by further template parameters that are deducible or have
  // default arguments ([temp.param]/11), e.g. std::_Tuple_impl's forwarding
  // constructor `template<class _UHead, class... _UTail, class = enable_if_t
  // <...>>`.  Locate the pack at whatever position it occupies and take its
  // arguments from the correspondingly-offset run of the flat template-argument
  // list: parameters before the pack occupy the leading argument slots, the
  // pack occupies the next (total_args - (num_params - 1)) slots, and any
  // trailing parameters occupy the remaining slots.  (When the pack is last --
  // the common case -- this reduces to the previous behaviour: start index =
  // num_params - 1, run to the end.)
  const auto &all_template_params = template_type.template_parameters();
  std::size_t template_pack_index = all_template_params.size();
  for(std::size_t i = 0; i < all_template_params.size(); ++i)
    if(all_template_params[i].get_bool(ID_ellipsis))
    {
      template_pack_index = i;
      break;
    }
  const bool has_template_pack =
    template_pack_index < all_template_params.size();

  std::vector<exprt> pack_arguments;
  bool pack_arguments_from_map = false;
  // N5008 [temp.variadic]/5,8: with MULTIPLE template parameter packs
  // (libc++ __tuple_impl's five-pack constructor), the positional
  // arithmetic below (`total - (num_params - 1)` slots at the FIRST
  // pack's index) cannot split the flat argument list between the
  // packs.  The FUNCTION parameter pack's elements are recorded
  // per-pack in the template map by deduction
  // (guess_function_template_args); source them from there.  Gated to
  // n_packs >= 2: single-pack shapes keep the positional path.
  if(has_template_pack)
  {
    std::size_t n_template_packs = 0;
    for(const auto &tp : all_template_params)
      if(tp.get_bool(ID_ellipsis))
        ++n_template_packs;
    if(n_template_packs >= 2 && !new_decl.declarators().empty())
    {
      // the function parameter pack's TYPE names its template pack
      // (e.g. `Up` in `Up&&... u`); walk to the innermost cpp_name
      const irept &fparams0 =
        new_decl.declarators()[0].type().find(ID_parameters);
      irep_idt fn_pack_short;
      for(const auto &fp : fparams0.get_sub())
      {
        if(fp.id() != ID_cpp_declaration)
          continue;
        const auto &d = static_cast<const cpp_declarationt &>(fp);
        if(
          d.declarators().empty() ||
          !d.declarators().front().type().get_bool(ID_ellipsis))
          continue;
        const typet merged = d.declarators().front().merge_type(d.type());
        const irept *t = &static_cast<const irept &>(merged);
        while(t->id() != ID_cpp_name && !t->get_sub().empty())
          t = &t->get_sub().front();
        if(t->id() == ID_cpp_name && !t->get_sub().empty())
          fn_pack_short = t->get_sub().front().get(ID_identifier);
      }
      if(!fn_pack_short.empty())
      {
        for(const auto &tp : all_template_params)
        {
          if(!tp.get_bool(ID_ellipsis) || tp.id() != ID_type)
            continue;
          const irep_idt pid = tp.type().get(ID_identifier);
          const std::string pid_str = id2string(pid);
          const auto pos = pid_str.rfind("::");
          if(
            (pos != std::string::npos ? pid_str.substr(pos + 2) : pid_str) !=
            id2string(fn_pack_short))
            continue;
          const auto pa_it = template_map.pack_args_map.find(pid);
          if(pa_it != template_map.pack_args_map.end())
          {
            for(const auto &t : pa_it->second)
              pack_arguments.push_back(exprt(ID_type, t));
            pack_arguments_from_map = true;
          }
          break;
        }
      }
    }
  }
  if(has_template_pack && !pack_arguments_from_map)
  {
    const std::size_t non_pack0 = all_template_params.size() - 1;
    const std::size_t total = full_template_args.arguments().size();
    if(total >= non_pack0)
    {
      const std::size_t pack_count = total - non_pack0;
      for(std::size_t j = template_pack_index;
          j < template_pack_index + pack_count && j < total;
          ++j)
      {
        const auto &pa = full_template_args.arguments()[j];
        if(pa.id() == ID_type && pa.type().id() == ID_empty)
          continue; // empty-pack sentinel
        pack_arguments.push_back(pa);
      }
    }
  }
  // N5008 [expr.prim.fold]/2: a fold over a ONE-element pack reduces to the
  // single instance of its pattern (for a binary fold, one application
  // against the init operand).  The general expansion below is skipped for
  // N == 1 (the parameter keeps its original name, so references need no
  // renaming), but fold NODES must still be rewritten: left in the body they
  // reach the C type-checker's residual-fold fallback, which degrades them to
  // `true` (wrong for any fold whose value matters, e.g. `(u, ...)`).
  if(has_template_pack && pack_arguments.size() == 1)
  {
    auto &func_decl = new_decl.declarators()[0];
    if(func_decl.value().is_not_nil())
    {
      std::function<void(irept &)> reduce_folds;
      reduce_folds = [&reduce_folds](irept &node)
      {
        if(
          (node.id() == irep_idt("cpp_right_fold") ||
           node.id() == irep_idt("cpp_left_fold")) &&
          !node.get_sub().empty())
        {
          // unary fold: the single pattern instance
          irept pattern = node.get_sub().front();
          reduce_folds(pattern);
          node = pattern;
          return;
        }
        if(
          node.id() == irep_idt("cpp_binary_fold") &&
          node.get_sub().size() >= 2)
        {
          // binary fold: one application of op against the init operand
          const irep_idt fold_op = node.get(irep_idt("fold_op"));
          irept bin(fold_op);
          irept init_expr = node.get_sub()[0];
          irept pattern = node.get_sub()[1];
          reduce_folds(init_expr);
          reduce_folds(pattern);
          bin.get_sub().push_back(init_expr);
          bin.get_sub().push_back(pattern);
          node = bin;
          return;
        }
        for(auto &sub : node.get_sub())
          reduce_folds(sub);
        for(auto &named : node.get_named_sub())
          reduce_folds(named.second);
      };
      reduce_folds(func_decl.value());
    }
  }
  if(has_template_pack && pack_arguments.size() != 1)
  {
    const std::size_t pack_sz = pack_arguments.size();

    // N5008 [expr.prim.fold]/3: with an EMPTY pack, a unary fold yields the
    // operator's identity (true for &&, false for ||; the comma fold yields
    // void(), approximated as 0) and a binary fold (init op ... op pack)
    // yields its init operand.  The pack parameter has already been removed
    // from the instantiated declaration at this point (pack_idx would be -1),
    // so the general expansion below -- which rewrites fold nodes -- never
    // runs and a residual fold would reach the C type-checker's fallback,
    // degrading to `true` with the function body otherwise lost.  Any fold
    // remaining in this body folds over this function's own (empty) pack:
    // folds over an enclosing class's pack were expanded during the class's
    // instantiation.
    if(pack_sz == 0 && !new_decl.declarators().empty())
    {
      auto &func_decl0 = new_decl.declarators()[0];
      if(func_decl0.value().is_not_nil())
      {
        std::function<void(irept &)> empty_folds;
        empty_folds = [&empty_folds](irept &node)
        {
          if(
            node.id() == irep_idt("cpp_right_fold") ||
            node.id() == irep_idt("cpp_left_fold"))
          {
            const irep_idt fold_op = node.get(irep_idt("fold_op"));
            if(fold_op == ID_and)
              node = true_exprt();
            else if(fold_op == ID_or)
              node = false_exprt();
            else
              node = from_integer(0, signed_int_type());
            return;
          }
          if(
            node.id() == irep_idt("cpp_binary_fold") && !node.get_sub().empty())
          {
            irept init_expr = node.get_sub()[0];
            empty_folds(init_expr);
            node = init_expr;
            return;
          }
          for(auto &sub : node.get_sub())
            empty_folds(sub);
          for(auto &named : node.get_named_sub())
            empty_folds(named.second);
        };
        empty_folds(func_decl0.value());
      }
    }

    auto &func_decl = new_decl.declarators()[0];
    irept &func_params = func_decl.type().add(ID_parameters);
    irept::subt &fp_sub = func_params.get_sub();

    // Find the pack parameter (last param with ellipsis on declarator)
    int pack_idx = -1;
    irep_idt pack_var_name;
    for(int i = static_cast<int>(fp_sub.size()) - 1; i >= 0; --i)
    {
      if(fp_sub[i].id() == ID_cpp_declaration)
      {
        const auto &d = to_cpp_declaration(fp_sub[i]);
        if(
          !d.declarators().empty() &&
          d.declarators().front().type().get_bool(ID_ellipsis))
        {
          pack_idx = i;
          const auto &dname = d.declarators().front().name();
          for(const auto &sub : dname.get_sub())
          {
            if(sub.id() == ID_name)
            {
              pack_var_name = sub.get(ID_identifier);
              break;
            }
          }
          break;
        }
      }
    }

    if(pack_idx >= 0 && !pack_var_name.empty())
    {
      // Build expanded parameters
      irept pack_param_template = fp_sub[pack_idx];
      // Remove ellipsis from template
      {
        auto &d = static_cast<cpp_declarationt &>(pack_param_template);
        d.declarators().front().type().remove(ID_ellipsis);
      }

      // N5008 [temp.variadic]/5, [dcl.ref]: the name of the type parameter
      // pack (e.g. `A` in `A&&... a`) and the deduced element type for each
      // expansion, so a forwarding-reference pack pattern in the body such as
      // `f(static_cast<A&&>(a)...)` can substitute the k-th deduced type for
      // `A` in lockstep with `a -> a$k`.
      irep_idt type_pack_name;
      {
        const typet &bt =
          static_cast<const cpp_declarationt &>(pack_param_template).type();
        if(
          bt.id() == ID_cpp_name && bt.get_sub().size() == 1 &&
          bt.get_sub().front().id() == ID_name)
          type_pack_name = bt.get_sub().front().get(ID_identifier);
      }
      std::vector<typet> pack_elem_types;
      for(std::size_t k = 0; k < pack_sz; ++k)
        pack_elem_types.push_back(
          pack_arguments[k].id() == ID_type ? pack_arguments[k].type()
                                            : typet{});

      std::vector<irep_idt> expanded_names;
      std::vector<irept> expanded_params;
      for(std::size_t k = 0; k < pack_sz; ++k)
      {
        irept param_copy = pack_param_template;
        const std::string new_name =
          id2string(pack_var_name) + "$" + std::to_string(k);
        expanded_names.push_back(irep_idt(new_name));

        // Set the parameter type from the k-th pack argument
        const exprt &pack_arg = pack_arguments[k];
        if(pack_arg.id() == ID_type)
        {
          auto &d = static_cast<cpp_declarationt &>(param_copy);
          d.type() = pack_arg.type();
        }

        // Rename the parameter
        auto &d = static_cast<cpp_declarationt &>(param_copy);
        if(!d.declarators().empty())
        {
          auto &dname = d.declarators().front().name();
          for(auto &sub : dname.get_sub())
          {
            if(sub.id() == ID_name)
            {
              sub.set(ID_identifier, new_name);
              break;
            }
          }
        }
        expanded_params.push_back(param_copy);
      }

      // Replace the pack parameter with expanded parameters
      fp_sub.erase(fp_sub.begin() + pack_idx);
      fp_sub.insert(
        fp_sub.begin() + pack_idx,
        expanded_params.begin(),
        expanded_params.end());

      // Expand pack references in the function body
      if(func_decl.value().is_not_nil())
      {
        // Helper: check if an irept is a cpp_name referencing pack_var
        auto is_pack_name = [&pack_var_name](const irept &n) -> bool
        {
          if(n.id() != ID_cpp_name)
            return false;
          for(const auto &s : n.get_sub())
          {
            if(s.id() == ID_name && s.get(ID_identifier) == pack_var_name)
              return true;
          }
          return false;
        };

        // Helper: make a cpp_name for an expanded parameter
        auto make_name = [](const irept &orig, const irep_idt &name)
        {
          irept copy = orig;
          for(auto &s : copy.get_sub())
          {
            if(s.id() == ID_name)
            {
              s.set(ID_identifier, name);
              break;
            }
          }
          return copy;
        };

        // Helper: check if an irept contains a pack_name anywhere
        std::function<bool(const irept &)> contains_pack_name;
        contains_pack_name = [&is_pack_name,
                              &contains_pack_name](const irept &n) -> bool
        {
          if(is_pack_name(n))
            return true;
          for(const auto &s : n.get_sub())
            if(contains_pack_name(s))
              return true;
          for(const auto &ns : n.get_named_sub())
            if(contains_pack_name(ns.second))
              return true;
          return false;
        };

        // Helper: substitute pack_name within an expression
        std::function<irept(const irept &, const irep_idt &)> substitute_pack;
        substitute_pack = [&is_pack_name, &make_name, &substitute_pack](
                            const irept &n, const irep_idt &name) -> irept
        {
          if(is_pack_name(n))
            return make_name(n, name);
          irept result = n;
          for(auto &s : result.get_sub())
            s = substitute_pack(s, name);
          return result;
        };

        std::function<void(irept &)> expand_pack;
        // N5008 [temp.variadic]/5, [dcl.ref]: substitute the type parameter
        // pack name with a concrete element type wherever it appears as a type
        // `cpp_name` in a pattern (e.g. the `A` in `static_cast<A&&>(...)`),
        // used in lockstep with substitute_pack for a forwarding-reference
        // pack pattern.  Replacing the `cpp_name A` inside the reference node
        // `A&&` with the deduced element type performs reference collapsing
        // (e.g. `int` -> `int&&`, `int&` -> `int&`).
        std::function<void(irept &, const typet &)> subst_type_pack;
        subst_type_pack =
          [&type_pack_name, &subst_type_pack](irept &n, const typet &elem)
        {
          auto matches = [&type_pack_name](const irept &m) -> bool
          {
            if(
              m.id() != ID_cpp_name || m.get_sub().size() != 1 ||
              m.get_sub().front().id() != ID_name)
              return false;
            const std::string nm =
              id2string(m.get_sub().front().get(ID_identifier));
            const auto p = nm.rfind("::");
            return (p != std::string::npos ? nm.substr(p + 2) : nm) ==
                   id2string(type_pack_name);
          };
          for(auto &s : n.get_sub())
          {
            if(matches(s))
              s = elem;
            else
              subst_type_pack(s, elem);
          }
          for(auto &ns : n.get_named_sub())
          {
            if(matches(ns.second))
              ns.second = elem;
            else
              subst_type_pack(ns.second, elem);
          }
        };
        expand_pack = [&expanded_names,
                       &expand_pack,
                       &is_pack_name,
                       &contains_pack_name,
                       &substitute_pack,
                       &make_name,
                       &type_pack_name,
                       &pack_elem_types,
                       &subst_type_pack](irept &node)
        {
          // Expand fold expressions
          if(
            (node.id() == irep_idt("cpp_right_fold") ||
             node.id() == irep_idt("cpp_left_fold")) &&
            !node.get_sub().empty() &&
            contains_pack_name(node.get_sub().front()))
          {
            const irep_idt fold_op = node.get(irep_idt("fold_op"));
            const irept &pack_expr = node.get_sub().front();
            bool is_left = (node.id() == irep_idt("cpp_left_fold"));

            // N5008 [expr.prim.fold]/3: a unary fold over an EMPTY pack
            // yields the operator's identity -- true for &&, false for ||,
            // void() for the comma operator (otherwise ill-formed).  Without
            // this the expansion below reads expanded_names[0] out of
            // bounds and the instantiation silently loses its body.
            // Mirrors the class-body fold expansion above.
            if(expanded_names.empty())
            {
              if(fold_op == ID_and)
                node = true_exprt();
              else if(fold_op == ID_or)
                node = false_exprt();
              else
                node = from_integer(0, signed_int_type());
              return;
            }

            if(expanded_names.size() == 1)
            {
              node = substitute_pack(pack_expr, expanded_names[0]);
              return;
            }

            // Build binary expression tree
            if(is_left)
            {
              // Left fold: ((a op b) op c)
              irept result = substitute_pack(pack_expr, expanded_names[0]);
              for(std::size_t i = 1; i < expanded_names.size(); ++i)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(result);
                bin.get_sub().push_back(
                  substitute_pack(pack_expr, expanded_names[i]));
                result = bin;
              }
              node = result;
            }
            else
            {
              // Right fold: (a op (b op c))
              irept result = substitute_pack(
                pack_expr, expanded_names[expanded_names.size() - 1]);
              for(int i = static_cast<int>(expanded_names.size()) - 2; i >= 0;
                  --i)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(
                  substitute_pack(pack_expr, expanded_names[i]));
                bin.get_sub().push_back(result);
                result = bin;
              }
              node = result;
            }
            return;
          }

          // Expand binary fold expressions: (init op ... op pack)
          if(
            node.id() == irep_idt("cpp_binary_fold") &&
            node.get_sub().size() >= 2 && contains_pack_name(node.get_sub()[1]))
          {
            const irep_idt fold_op = node.get(irep_idt("fold_op"));
            const irept &init_expr = node.get_sub()[0];
            const irept &pack_expr = node.get_sub()[1];

            // Binary left fold: ((init op pack[0]) op pack[1]) op ...
            irept result = init_expr;
            for(std::size_t i = 0; i < expanded_names.size(); ++i)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(result);
              bin.get_sub().push_back(
                substitute_pack(pack_expr, expanded_names[i]));
              result = bin;
            }
            node = result;
            return;
          }

          // Look for function call arguments containing pack_var...
          if(
            node.id() == ID_side_effect &&
            node.get(ID_statement) == ID_function_call)
          {
            for(auto &sub : node.get_sub())
            {
              if(sub.id() != ID_arguments)
                continue;
              irept::subt &arg_sub = sub.get_sub();
              irept::subt new_args;
              for(auto &a : arg_sub)
              {
                if(is_pack_name(a))
                {
                  // Expand into individual arguments
                  for(const auto &ename : expanded_names)
                    new_args.push_back(make_name(a, ename));
                }
                else if(a.get_bool(ID_ellipsis) && contains_pack_name(a))
                {
                  // N5008 [temp.variadic]/5: a pack-expansion call argument
                  // whose pattern CONTAINS (but is not exactly) the value pack
                  // -- e.g. a perfect-forwarding `static_cast<A&&>(a)...` (the
                  // body of variadic std::__invoke) -- expands to one argument
                  // per element.  In the k-th copy substitute the value pack
                  // `a -> a$k` and, in lockstep, the type pack `A -> ` the k-th
                  // deduced element type ([dcl.ref] reference collapsing).
                  for(std::size_t k = 0; k < expanded_names.size(); ++k)
                  {
                    irept copy = substitute_pack(a, expanded_names[k]);
                    copy.remove(ID_ellipsis);
                    if(
                      !type_pack_name.empty() && k < pack_elem_types.size() &&
                      pack_elem_types[k].is_not_nil())
                      subst_type_pack(copy, pack_elem_types[k]);
                    new_args.push_back(copy);
                  }
                }
                else
                {
                  new_args.push_back(a);
                }
              }
              arg_sub = new_args;
              break;
            }
          }

          // N5008 [temp.variadic]/5 + [dcl.init.aggr]/... : a pack expansion in
          // a BRACED / aggregate initializer, e.g. `box{fwd(e)...}` (the shape
          // of std::make_tuple / the tuple forwarding constructor,
          // `tuple<...>(std::forward<E>(a)...)`).  Mirror the function-call
          // argument branch above: replicate each pack-expansion element (a
          // bare pack name, or a `...`-carrying pattern that CONTAINS the pack
          // such as `fwd(e)`) into one element per pack member.  Without this
          // the recursion descends into the element `fwd(e)` and the
          // function-call branch wrongly expands its argument `e` in place
          // (yielding a single `fwd(e$0, e$1)` that retains the `...`), so the
          // enclosing function-template body fails to convert and is dropped.
          if(node.id() == ID_initializer_list)
          {
            irept::subt &elems = node.get_sub();
            irept::subt new_elems;
            for(auto &a : elems)
            {
              if(is_pack_name(a))
              {
                for(const auto &ename : expanded_names)
                  new_elems.push_back(make_name(a, ename));
              }
              else if(a.get_bool(ID_ellipsis) && contains_pack_name(a))
              {
                for(std::size_t k = 0; k < expanded_names.size(); ++k)
                {
                  irept copy = substitute_pack(a, expanded_names[k]);
                  copy.remove(ID_ellipsis);
                  if(
                    !type_pack_name.empty() && k < pack_elem_types.size() &&
                    pack_elem_types[k].is_not_nil())
                    subst_type_pack(copy, pack_elem_types[k]);
                  new_elems.push_back(copy);
                }
              }
              else
              {
                new_elems.push_back(a);
              }
            }
            elems = new_elems;
          }

          // Expand lambda pack init-captures: [...x = args]
          if(node.id() == irep_idt("lambda"))
          {
            irept &cap_list = node.add("lambda_capture");
            irept::subt new_caps;
            irep_idt cap_pack_name;
            std::vector<irep_idt> cap_expanded_names;
            for(auto &cap : cap_list.get_sub())
            {
              if(
                cap.get_bool("is_pack") && contains_pack_name(cap.find("init")))
              {
                cap_pack_name = cap.get(ID_identifier);
                for(std::size_t i = 0; i < expanded_names.size(); ++i)
                {
                  irept new_cap = cap;
                  new_cap.remove("is_pack");
                  irep_idt ename =
                    id2string(cap_pack_name) + "_" + std::to_string(i);
                  new_cap.set(ID_identifier, ename);
                  new_cap.add("init") =
                    substitute_pack(cap.find("init"), expanded_names[i]);
                  new_caps.push_back(new_cap);
                  cap_expanded_names.push_back(ename);
                }
              }
              else
              {
                new_caps.push_back(cap);
              }
            }
            cap_list.get_sub() = new_caps;

            // Expand fold expressions in the lambda body that reference
            // the captured pack name.
            if(!cap_pack_name.empty())
            {
              auto is_cap_name = [&cap_pack_name](const irept &n) -> bool
              {
                if(n.id() != ID_cpp_name)
                  return false;
                for(const auto &s : n.get_sub())
                  if(s.id() == ID_name && s.get(ID_identifier) == cap_pack_name)
                    return true;
                return false;
              };
              auto make_cap_name = [](const irept &orig, const irep_idt &name)
              {
                irept copy = orig;
                for(auto &s : copy.get_sub())
                  if(s.id() == ID_name)
                  {
                    s.set(ID_identifier, name);
                    break;
                  }
                return copy;
              };
              auto sub_cap =
                [&is_cap_name, &make_cap_name](
                  const irept &n, const irep_idt &name, auto &self) -> irept
              {
                if(is_cap_name(n))
                  return make_cap_name(n, name);
                irept result = n;
                for(auto &s : result.get_sub())
                  s = self(s, name, self);
                return result;
              };
              auto contains_cap =
                [&is_cap_name](const irept &n, auto &self) -> bool
              {
                if(is_cap_name(n))
                  return true;
                for(const auto &s : n.get_sub())
                  if(self(s, self))
                    return true;
                for(const auto &ns : n.get_named_sub())
                  if(self(ns.second, self))
                    return true;
                return false;
              };

              std::function<void(irept &)> expand_cap_fold;
              expand_cap_fold = [&](irept &n)
              {
                if(
                  (n.id() == irep_idt("cpp_right_fold") ||
                   n.id() == irep_idt("cpp_left_fold")) &&
                  !n.get_sub().empty() &&
                  contains_cap(n.get_sub().front(), contains_cap))
                {
                  const irep_idt fold_op = n.get(irep_idt("fold_op"));
                  const irept &pe = n.get_sub().front();
                  bool is_left = (n.id() == irep_idt("cpp_left_fold"));
                  if(cap_expanded_names.size() == 1)
                  {
                    n = sub_cap(pe, cap_expanded_names[0], sub_cap);
                    return;
                  }
                  if(is_left)
                  {
                    irept r = sub_cap(pe, cap_expanded_names[0], sub_cap);
                    for(std::size_t i = 1; i < cap_expanded_names.size(); ++i)
                    {
                      irept bin(fold_op);
                      bin.get_sub().push_back(r);
                      bin.get_sub().push_back(
                        sub_cap(pe, cap_expanded_names[i], sub_cap));
                      r = bin;
                    }
                    n = r;
                  }
                  else
                  {
                    irept r = sub_cap(
                      pe,
                      cap_expanded_names[cap_expanded_names.size() - 1],
                      sub_cap);
                    for(int i = static_cast<int>(cap_expanded_names.size()) - 2;
                        i >= 0;
                        --i)
                    {
                      irept bin(fold_op);
                      bin.get_sub().push_back(
                        sub_cap(pe, cap_expanded_names[i], sub_cap));
                      bin.get_sub().push_back(r);
                      r = bin;
                    }
                    n = r;
                  }
                  return;
                }
                // Binary fold: (init op ... op pack)
                if(
                  n.id() == irep_idt("cpp_binary_fold") &&
                  n.get_sub().size() >= 2 &&
                  contains_cap(n.get_sub()[1], contains_cap))
                {
                  const irep_idt fold_op = n.get(irep_idt("fold_op"));
                  const irept &init_e = n.get_sub()[0];
                  const irept &pe = n.get_sub()[1];
                  irept r = init_e;
                  for(std::size_t i = 0; i < cap_expanded_names.size(); ++i)
                  {
                    irept bin(fold_op);
                    bin.get_sub().push_back(r);
                    bin.get_sub().push_back(
                      sub_cap(pe, cap_expanded_names[i], sub_cap));
                    r = bin;
                  }
                  n = r;
                  return;
                }
                for(auto &s : n.get_sub())
                  expand_cap_fold(s);
                for(auto &ns : n.get_named_sub())
                  expand_cap_fold(ns.second);
              };
              // The lambda body is a named sub-tree
              for(auto &ns : node.get_named_sub())
                expand_cap_fold(ns.second);
              for(auto &s : node.get_sub())
                expand_cap_fold(s);
            }
          }

          // N5008 [temp.variadic]/5: a pack expansion in the expression-list
          // of a declarator's direct-initializer, e.g.
          // `_Up tmp(forward<_Args>(__args)...)` (the allocator
          // `construct` body behind std::map's node construction).  Mirror
          // the function-call argument branch: replicate each `...`-carrying
          // pattern into one initializer per pack element, substituting the
          // value pack `a -> a$k` and the type pack in lockstep.  Without
          // this the recursion descends into the pattern and the
          // function-call branch wrongly expands the INNER argument list in
          // place (a single `forward<_Args>(__args$0, __args$1)` that keeps
          // its `...`), so the enclosing body fails to convert and is
          // dropped.
          // N5008 [temp.variadic]/5 + [expr.new]: a pack expansion in a
          // new-initializer's expression-list inside this function-template
          // body -- `::new((void*)__location) _Tp(forward<_Args>(__args)...)`,
          // the C++20 std::construct_at body ([specialized.construct]) that
          // the C++20 headers route std::map's node construction through.
          // Mirror the function-call argument branch: replicate each
          // `...`-carrying pattern into one initializer per pack element,
          // substituting the value pack `a -> a$k` and the type pack in
          // lockstep.  Without this the recursion descends into the pattern
          // and the function-call branch expands the INNER argument list in
          // place (one `forward<_Args>(__args$0, __args$1)` keeping its
          // `...`), so the body fails to convert and is dropped -- the
          // constructed object keeps garbage.
          if(
            node.id() == ID_side_effect && node.get(ID_statement) == ID_cpp_new)
          {
            irept &init = node.add(ID_initializer);
            irept::subt &in_sub = init.get_sub();
            if(!in_sub.empty())
            {
              irept::subt new_in;
              for(auto &a : in_sub)
              {
                if(is_pack_name(a))
                {
                  for(const auto &ename : expanded_names)
                    new_in.push_back(make_name(a, ename));
                }
                else if(a.get_bool(ID_ellipsis) && contains_pack_name(a))
                {
                  for(std::size_t k = 0; k < expanded_names.size(); ++k)
                  {
                    irept copy = substitute_pack(a, expanded_names[k]);
                    copy.remove(ID_ellipsis);
                    if(
                      !type_pack_name.empty() && k < pack_elem_types.size() &&
                      pack_elem_types[k].is_not_nil())
                      subst_type_pack(copy, pack_elem_types[k]);
                    new_in.push_back(copy);
                  }
                }
                else
                {
                  new_in.push_back(a);
                }
              }
              in_sub = new_in;
            }
          }

          if(
            node.id() == ID_cpp_declarator &&
            node.find(ID_init_args).is_not_nil())
          {
            // Use find-then-add: irept::add would CREATE an empty
            // ID_init_args entry on every declarator visited, including one
            // initialised with `= value` -- typecheck_decl later rejects a
            // declarator carrying both a value and init_args (invariant
            // "declarator should not have init_args"; dog-fooding CBMC's
            // own invariant.h crashed on `std::string backtrace = ...`
            // inside the variadic report_invariant_failure chain).
            irept &init_args = node.add(ID_init_args);
            irept::subt &ia_sub = init_args.get_sub();
            if(!ia_sub.empty())
            {
              irept::subt new_ia;
              for(auto &a : ia_sub)
              {
                if(is_pack_name(a))
                {
                  for(const auto &ename : expanded_names)
                    new_ia.push_back(make_name(a, ename));
                }
                else if(a.get_bool(ID_ellipsis) && contains_pack_name(a))
                {
                  for(std::size_t k = 0; k < expanded_names.size(); ++k)
                  {
                    irept copy = substitute_pack(a, expanded_names[k]);
                    copy.remove(ID_ellipsis);
                    if(
                      !type_pack_name.empty() && k < pack_elem_types.size() &&
                      pack_elem_types[k].is_not_nil())
                      subst_type_pack(copy, pack_elem_types[k]);
                    new_ia.push_back(copy);
                  }
                }
                else
                {
                  new_ia.push_back(a);
                }
              }
              ia_sub = new_ia;
            }
          }

          for(auto &sub : node.get_sub())
            expand_pack(sub);
          for(auto &named : node.get_named_sub())
            expand_pack(named.second);
        };
        expand_pack(func_decl.value());
      }
    }
  }

  // Per [temp.variadic]/7: remove empty pack expansions
  if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
  {
    // Per [basic.scope.temp] and [temp.variadic]/5: a pack parameter's
    // short name in this template refers to THIS template's pack
    // parameter, not a pack with the same short name declared by
    // some other template that happens to be in the pack_size_map.
    // Restrict to packs declared by the template being instantiated
    // so that `_Types` from one template doesn't cause parameters of
    // another template to be stripped.
    std::set<irep_idt> local_pack_ids;
    for(const auto &tp : template_type.template_parameters())
    {
      if(tp.get_bool(ID_ellipsis))
      {
        irep_idt pid = tp.type().get(ID_identifier);
        if(!pid.empty())
          local_pack_ids.insert(pid);
      }
    }
    std::set<std::string> ep;
    for(const auto &ps : template_map.pack_size_map)
      if(ps.second == 0 && local_pack_ids.count(ps.first))
      {
        const std::string f = id2string(ps.first);
        auto p = f.rfind("::");
        ep.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
    if(!ep.empty())
    {
      std::function<bool(const irept &)> has_ep = [&](const irept &n) -> bool
      {
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &s : n.get_sub())
          if(has_ep(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(has_ep(ns.second))
            return true;
        return false;
      };
      auto &dt = new_decl.declarators()[0].type();
      if(dt.id() == ID_function_type)
      {
        irept &params = dt.add(ID_parameters);
        params.get_sub().erase(
          std::remove_if(
            params.get_sub().begin(),
            params.get_sub().end(),
            [&](const irept &p)
            {
              if(p.id() != ID_cpp_declaration)
                return false;
              // N5008 [temp.variadic]/7: only a *function parameter pack*
              // -- a parameter declared with a top-level `...`, e.g.
              // `_T... args` -- expands to an empty parameter list when the
              // pack is empty and is therefore removed.  A parameter whose
              // type merely *contains* the empty pack nested inside a
              // template-argument pack expansion (e.g. `Base<_H, _T...>
              // &__b`) is a single parameter: the empty expansion collapses
              // the argument list to `Base<_H>`, but the parameter itself
              // must be kept (removing it leaves the instantiated function
              // with no parameter and an unbindable call -- see
              // regression/cbmc-cpp/cpp11_derived_to_base_pack_call_in_body).
              // Detect a genuine parameter pack by the top-level ellipsis on
              // the declarator/type only; do NOT remove on a mere nested
              // occurrence of the pack name.
              for(const auto &d : p.get_sub())
              {
                if(
                  d.id() == ID_cpp_declarator &&
                  (d.find(ID_type).get_bool(ID_ellipsis) ||
                   d.get_bool(ID_ellipsis)))
                  return true;
              }
              return false;
            }),
          params.get_sub().end());
      }
      irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
      for(auto &init : mi.get_sub())
      {
        auto &subs = init.get_sub();
        subs.erase(
          std::remove_if(
            subs.begin(),
            subs.end(),
            [&](const irept &s) { return has_ep(s); }),
          subs.end());
      }
    }
  }

  // N5008 [temp.point]/1, [temp.inst]/1/5: convert the instantiated free
  // function-template specialization.  This registers its *declaration* (the
  // signature, which is all a reference and overload resolution need per
  // [temp.inst]/1) and -- because the instance is a non-template, non-`auto`
  // function -- DEFERS its *definition* (body) to the `method_bodies` queue via
  // `cpp_declarator_convertert` -> `add_method_body`.  The deferred drain in
  // `typecheck_method_bodies` is CBMC's point-of-instantiation approximation,
  // so the body is converted there in a clean top-level context, not nested in
  // the referencing body's conversion.  (The earlier
  // `cpp11_derived_to_base_pack_call_in_body` defect was NOT here: it was the
  // empty-trailing-pack parameter being dropped from `new_decl` above, fixed by
  // restricting empty-pack parameter removal to genuine function parameter
  // packs per [temp.variadic]/7.  See
  // doc/architectural/cpp-frontend-review-2026-06-23-instantiation-context.md.)
  convert_non_template_declaration(new_decl);

  const symbolt &symb = lookup(new_decl.declarators()[0].get(ID_identifier));

  return symb;
}

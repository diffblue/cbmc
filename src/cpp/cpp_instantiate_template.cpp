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
#include <util/base_exceptions.h> // IWYU pragma: keep
#include <util/c_types.h>
#include <util/simplify_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_type2name.h"
#include "cpp_typecheck_resolve.h"

#include <algorithm>

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
              const symbolt &symbol =
                lookup(to_symbol_expr(node).get_identifier());
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

      make_constant(e);

      // this must be a constant, which includes true/false
      mp_integer i;

      if(e == true)
        i=1;
      else if(e == false)
        i=0;
      else
      {
        // follow c_enum_tag to c_enum for to_integer
        if(e.type().id() == ID_c_enum_tag)
          e.type() = follow_tag(to_c_enum_tag_type(e.type()));

        if(to_integer(to_constant_expr(e), i))
        {
          error().source_location = expr.find_source_location();
          error() << "template argument expression expected to be "
                  << "scalar constant, but got '" << to_string(e) << "'" << eom;
          throw 0;
        }
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
    out << "instantiating '" << symbol.pretty_name << "' with <";

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

const symbolt &cpp_typecheckt::class_template_symbol(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_tct &specialization_template_args,
  const cpp_template_args_tct &full_template_args)
{
  if(full_template_args.has_unassigned())
  {
    // Some template arguments could not be resolved (e.g., default
    // arguments that depend on unresolved types). Treat as an error
    // rather than crashing.
    error().source_location = source_location;
    error() << "template '" << template_symbol.base_name
            << "' has unresolved template arguments" << eom;
    throw 0;
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
  std::string suffix=template_suffix(full_template_args);

  cpp_scopet *template_scope=
    static_cast<cpp_scopet *>(cpp_scopes.id_map[template_symbol.name]);

  INVARIANT_STRUCTURED(
    template_scope!=nullptr, nullptr_exceptiont, "template_scope is null");

  irep_idt identifier = id2string(template_scope->get_parent().prefix) +
                        "tag-" + id2string(template_symbol.base_name) +
                        id2string(suffix);

  // already there?
  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find(identifier);
  if(s_it!=symbol_table.symbols.end())
    return s_it->second;

  // Create as incomplete struct, but mark as
  // "template_class_instance", to be elaborated later.
  type_symbolt new_symbol{identifier, struct_typet(), template_symbol.mode};
  new_symbol.pretty_name=template_symbol.pretty_name;
  new_symbol.location=template_symbol.location;
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
  new_symbol.base_name=template_symbol.base_name;

  symbolt *s_ptr;
  symbol_table.move(new_symbol, s_ptr);

  // put into template scope
  cpp_idt &id=cpp_scopes.put_into_scope(*s_ptr, *template_scope);

  id.id_class=cpp_idt::id_classt::CLASS;
  id.is_scope=true;
  id.prefix = template_scope->get_parent().prefix +
              id2string(s_ptr->base_name) + id2string(suffix) + "::";
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
    const symbolt &primary_template = lookup(t_type.get(ID_identifier));

    // If this class template is already being instantiated (on the
    // instantiation stack), skip elaboration to break infinite
    // recursion.
    for(const auto &entry : instantiation_stack)
    {
      if(entry.identifier == primary_template.name)
        return;
    }

    const cpp_template_args_tct &specialization_args =
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_specialization_template_args));
    const cpp_template_args_tct &full_args =
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_full_template_args));

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

    // Search for a better-matching partial specialization only if
    // the symbol was created with the primary template (not already
    // matched to a partial specialization).
    const symbolt *best_match = &primary_template;
    cpp_template_args_tct best_spec_args = specialization_args;

    if(primary_template.type.get(ID_specialization_of).empty())
    {
      cpp_scopet *template_scope =
        static_cast<cpp_scopet *>(cpp_scopes.id_map[primary_template.name]);

      if(template_scope != nullptr)
      {
        cpp_scopet &scope = template_scope->get_parent();
        cpp_scopet::id_sett id_set =
          scope.lookup(primary_template.base_name, cpp_scopet::SCOPE_ONLY);

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
            continue;
          }

          cpp_saved_template_mapt saved_map(template_map);
          cpp_save_scopet save_scope(cpp_scopes);

          template_map.build_unassigned(cpp_declaration.template_type());

          cpp_scopet *spec_scope =
            static_cast<cpp_scopet *>(cpp_scopes.id_map[s.name]);
          if(spec_scope != nullptr)
            cpp_scopes.go_to(*spec_scope);

          cpp_typecheck_resolvet resolver(*this);

          for(std::size_t i = 0; i < full_args_tc.arguments().size(); i++)
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

          cpp_template_args_tct guessed_args =
            template_map.build_template_args(cpp_declaration.template_type());

          if(guessed_args.has_unassigned())
            continue;

          // Typecheck the partial specialization args with the guessed
          // values, using the primary template for type context.
          // If typechecking fails (e.g., accessing a member of a
          // non-class type), treat it as a substitution failure
          // (SFINAE) and skip this specialization.
          cpp_template_args_tct partial_specialization_args_tc;
          bool sfinae_failed = false;
          {
            null_message_handlert null_handler;
            message_handlert &old_handler = get_message_handler();
            set_message_handler(null_handler);
            try
            {
              partial_specialization_args_tc = typecheck_template_args(
                type.source_location(),
                primary_template,
                partial_specialization_args);
            }
            catch(...)
            {
              sfinae_failed = true;
            }
            set_message_handler(old_handler);
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

          if(partial_specialization_args_tc == full_args_tc)
          {
            // operator== on irept ignores #-prefixed attributes like
            // C_constant and C_volatile. Check them explicitly.
            bool qualifiers_match = true;
            for(std::size_t j = 0;
                j < partial_specialization_args_tc.arguments().size();
                j++)
            {
              const exprt &p = partial_specialization_args_tc.arguments()[j];
              const exprt &f = full_args_tc.arguments()[j];
              if(p.id() == ID_type)
              {
                if(
                  p.type().get_bool(ID_C_constant) !=
                    f.type().get_bool(ID_C_constant) ||
                  p.type().get_bool(ID_C_volatile) !=
                    f.type().get_bool(ID_C_volatile))
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
            }
          }
        }
      }
    }

    instantiate_template(
      type.source_location(), *best_match, best_spec_args, full_args);
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
    show_instantiation_stack(error());
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
  if(specialization_template_args.has_unassigned())
  {
    error().source_location = source_location;
    error() << "internal error: template parameter without instance:\n"
            << template_symbol.name << eom;
    throw 0;
  }
  DATA_INVARIANT(
    !full_template_args.has_unassigned(), "should never get 'unassigned' here");

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
  cpp_scopet &sub_scope = sub_scope_for_instantiation(*template_scope, suffix);

  // let's see if we have the instance already
  {
    cpp_scopet::id_sett id_set =
      sub_scope.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

    if(id_set.size()==1)
    {
      // It has already been instantiated!
      const cpp_idt &cpp_id = **id_set.begin();

      DATA_INVARIANT(
        cpp_id.id_class == cpp_idt::id_classt::CLASS ||
          cpp_id.id_class == cpp_idt::id_classt::TYPEDEF ||
          cpp_id.id_class == cpp_idt::id_classt::SYMBOL,
        "id must be class, typedef, or symbol");

      const symbolt &symb=lookup(cpp_id.identifier);

      // continue if the type is incomplete only
      if(cpp_id.id_class==cpp_idt::id_classt::CLASS &&
         symb.type.id()==ID_struct)
        return symb;
      else if(cpp_id.id_class == cpp_idt::id_classt::TYPEDEF)
        return symb;
      else if(symb.value.is_not_nil())
        return symb;
    }
    else if(new_decl.type().id() == ID_struct)
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
        s_it->second.type.id() == ID_struct &&
        !to_struct_type(s_it->second.type).is_incomplete())
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
    // Switch to the sub-scope so that typecheck_compound_type creates
    // the class symbol with an identifier that includes the template
    // suffix, matching the identifier used by class_template_symbol.
    cpp_scopes.go_to(sub_scope);

    // a class template
    convert_non_template_declaration(new_decl);

    // Restore the template scope for template method processing.
    saved_scope.restore();
    cpp_scopes.go_to(*template_scope);

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
        continue;

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

      // Apply the template map to substitute template parameters
      // (e.g. _Dom, _Tp) with the actual types in the method
      // declaration before converting it.
      // First, type-check the declaration type in the method's
      // template scope so that template parameter names (cpp_name)
      // are resolved to template_parameter_symbol_type, then apply
      // the template map to replace them with actual types.
      if(method_decl.type().id() == ID_cpp_name)
      {
        typecheck_type(method_decl.type());
        template_map.apply(method_decl.type());
      }

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

  if(is_template_method && !new_decl.is_typedef())
  {
    symbolt &symb = symbol_table.get_writeable_ref(class_name);

    PRECONDITION(new_decl.declarators().size() == 1);

    if(new_decl.member_spec().is_virtual())
    {
      error().source_location=new_decl.source_location();
      error() << "invalid use of `virtual' in template declaration"
              << eom;
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

    CHECK_RETURN(!access.empty());
    PRECONDITION(symb.type.id() == ID_struct);

    typecheck_compound_declarator(
      symb,
      new_decl,
      new_decl.declarators()[0],
      to_struct_type(symb.type).components(),
      access,
      is_static,
      false,
      false);

    const symbolt &method_sym =
      lookup(to_struct_type(symb.type).components().back().get_name());

    // The method was added to deferred_typechecking by
    // typecheck_compound_declarator (because the parent scope is a template
    // scope). Since we are actually instantiating this method, move it
    // from deferred_typechecking to method_bodies so the body gets
    // type-checked and is not erased during clean_up.
    if(deferred_typechecking.erase(method_sym.name))
      add_method_body(&symbol_table.get_writeable_ref(method_sym.name));

    return method_sym;
  }

  // not a class template, not a class template method,
  // it must be a function template, a template alias, or a variable template!

  PRECONDITION(new_decl.declarators().size() == 1);

  // Variable template: the declarator type is not a function type.
  // Instantiate by converting the declaration directly.
  if(
    !new_decl.declarators().empty() &&
    new_decl.declarators()[0].type().id() != ID_function_type &&
    new_decl.type().id() != ID_struct && !new_decl.is_typedef())
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

      cpp_scopet *ts =
        static_cast<cpp_scopet *>(cpp_scopes.id_map[template_symbol.name]);
      if(ts != nullptr)
      {
        cpp_scopet &parent_scope = ts->get_parent();
        cpp_scopet::id_sett id_set = parent_scope.lookup(
          template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

        const symbolt *best_match = nullptr;
        cpp_template_args_tct best_spec_args;

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

          cpp_scopet *spec_scope =
            static_cast<cpp_scopet *>(cpp_scopes.id_map[s.name]);
          if(spec_scope != nullptr)
            cpp_scopes.go_to(*spec_scope);

          cpp_typecheck_resolvet resolver(*this);

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

          if(guessed.has_unassigned())
            continue;

          cpp_template_args_tct partial_tc;
          bool sfinae_failed = false;
          {
            null_message_handlert null_handler;
            message_handlert &old_handler = get_message_handler();
            set_message_handler(null_handler);
            try
            {
              partial_tc = typecheck_template_args(
                source_location, template_symbol, partial_args);
            }
            catch(...)
            {
              sfinae_failed = true;
            }
            set_message_handler(old_handler);
          }
          if(sfinae_failed)
            continue;

          if(partial_tc == full_args_resolved)
          {
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

    convert_non_template_declaration(new_decl);

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
  // list is shorter than the parameter list), remove pack-expanded
  // parameters from the function declaration and its nested types.
  if(
    full_template_args.arguments().size() <
      template_type.template_parameters().size() &&
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
    // Strip pack variable references from function call arguments in body
    if(!pack_var_name.empty() && func_decl.value().is_not_nil())
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
                    if(a.id() == ID_cpp_name)
                    {
                      for(const auto &s : a.get_sub())
                      {
                        if(
                          s.id() == ID_name &&
                          s.get(ID_identifier) == pack_var_name)
                          return true;
                      }
                    }
                    return false;
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
      strip_pack_var(func_decl.value());
    }
  }

  convert_non_template_declaration(new_decl);

  const symbolt &symb=
    lookup(new_decl.declarators()[0].get(ID_identifier));

  return symb;
}

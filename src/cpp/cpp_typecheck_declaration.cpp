/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\********************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/c_types.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>

#include "cpp_declarator_converter.h"
#include "cpp_template_type.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"

std::optional<typet> cpp_typecheckt::deduce_class_template_arguments(
  const cpp_namet &class_template_name,
  const std::vector<exprt> &args)
{
  // [dcl.type.class.deduct]: deduction only applies to a class-template-id
  // written *without* a template-argument-list.
  for(const auto &sub : class_template_name.get_sub())
    if(sub.id() == ID_template_args)
      return {};

  // The name must denote a class template.  A class that is itself not a
  // template but has a constructor template (e.g. libstdc++'s
  // `__max_size_type`, with `template<class T> __max_size_type(T)`) also has a
  // TEMPLATE-classed scope entry, but that entry is a *function* template; it
  // does not make `C{...}` a class-template-argument-deduction context
  // ([dcl.type.class.deduct] applies only to a class template).  Require the
  // entry to denote an actual class template, so an ordinary construction of
  // such a class (notably `C{...}` written inside C's own members, where the
  // injected-class-name makes the constructor template visible under the bare
  // name) falls through to a normal constructor call instead.
  const cpp_idt *template_id = nullptr;
  cpp_scopet::id_sett id_set;
  {
    // The base name is looked up in the current scope; for a qualified
    // class-template-id (e.g. `std::optional`) first resolve the qualification
    // to its scope and look the base name up there.  Without this, CTAD for a
    // qualified class template failed (`std::optional(x)` -> "found no match").
    cpp_save_scopet save_scope(cpp_scopes);
    if(class_template_name.is_qualified())
    {
      try
      {
        cpp_typecheck_resolvet resolver(*this);
        irep_idt qbase;
        cpp_template_args_non_tct qargs;
        resolver.resolve_scope(class_template_name, qbase, qargs);
        id_set = cpp_scopes.current_scope().lookup(
          qbase, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);
      }
      catch(...)
      {
        return {};
      }
    }
    else
    {
      id_set = cpp_scopes.current_scope().lookup(
        class_template_name.get_base_name(), cpp_scopet::RECURSIVE);
    }

    for(const auto *id : id_set)
    {
      if(id->id_class != cpp_idt::id_classt::TEMPLATE)
        continue;
      const symbolt *id_sym = symbol_table.lookup(id->identifier);
      if(
        id_sym != nullptr && id_sym->type.id() == ID_cpp_declaration &&
        to_cpp_declaration(id_sym->type).is_class_template())
      {
        template_id = id;
        break;
      }
    }
  }
  if(template_id == nullptr)
    return {};


  // The template's type parameters, noting a trailing parameter pack.
  std::vector<bool> param_is_pack;
  {
    const symbolt &sym = lookup(template_id->identifier);
    const auto &tmpl_type =
      static_cast<const template_typet &>(sym.type.find(ID_template_type));
    for(const auto &p : tmpl_type.template_parameters())
      if(p.id() == ID_type)
        param_is_pack.push_back(p.get_bool(ID_ellipsis));
  }
  const std::size_t n_type_params = param_is_pack.size();
  const bool has_pack = n_type_params != 0 && param_is_pack.back();

  // Type-check the initializer arguments to obtain their types.  An
  // argument that has already been type-checked (the function-call
  // route type-checks arguments before re-routing to CTAD; a lowered
  // aggregate VALUE has no second-round handler) is used as-is.
  std::vector<typet> arg_types;
  std::vector<bool> arg_is_lvalue;
  for(const auto &a : args)
  {
    exprt arg = a;
    if(arg.type().is_nil() || arg.type().id().empty())
      typecheck_expr(arg);
    arg_types.push_back(arg.type());
    arg_is_lvalue.push_back(arg.get_bool(ID_C_lvalue));
  }

  // N5008 [temp.deduct.call]/2-3 adjustments of A before deducing
  // against a (hypothetical or explicit) guide's parameter P
  // ([over.match.class.deduct]/1: each guide deduces as a function
  // call): when P is NOT a reference, an array argument decays to a
  // pointer, a function to a function pointer, and top-level cv is
  // dropped; when P is a FORWARDING reference and the argument an
  // lvalue, A is `lvalue reference to A`.  Without the decay,
  // constructor-pattern deduction (e.g. `wrap(base_, 1)` with a member
  // of type int(&)[1] against `wrap(I, int)`) yielded wrap<int[1]>
  // instead of wrap<int*>; the mistyped member broke the goto program
  // downstream (simplify_rec postcondition).
  const auto adjust_deduction_arg =
    [this](const typet &pattern, const typet &arg_type, bool is_lvalue) {
      const bool pattern_is_ref = pattern.id() == ID_frontend_pointer &&
                                  (pattern.get_bool(ID_C_reference) ||
                                   pattern.get_bool(ID_C_rvalue_reference));
      typet at = arg_type;
      if(!pattern_is_ref)
      {
        if(is_reference(at))
          at = to_reference_type(at).base_type();
        if(at.id() == ID_array)
          at = pointer_type(to_array_type(at).element_type());
        else if(at.id() == ID_code)
          at = pointer_type(at);
        at.remove(ID_C_constant);
      }
      else if(
        pattern.get_bool(ID_C_rvalue_reference) &&
        to_type_with_subtype(pattern).subtype().id() == ID_cpp_name &&
        is_lvalue && !is_reference(at) && !is_rvalue_reference(at))
      {
        at = reference_type(at);
      }
      return at;
    };

  // Explicit deduction guides ([temp.deduct.guide], [over.match.class.deduct]):
  // a guide is one of the entries the class name resolves to whose declarator
  // was flagged at parse time (its constructor-like declaration carried a
  // trailing return type) and whose declaration type is the guided
  // specialization `C<...>`.  For the first guide whose parameter count matches
  // the argument count, deduce the guide's own template parameters from the
  // argument types ([temp.deduct.type]) and instantiate the guide's return
  // type, yielding the deduced specialization.  This honours guides that
  // transform the arguments (`S(T) -> S<T*>`), add fixed arguments
  // (`P(T) -> P<T, int>`) or ignore leading parameters (`V(int, T) -> V<T>`),
  // none of which the positional fallback below can express.
  for(const auto *gid : id_set)
  {
    if(gid->id_class != cpp_idt::id_classt::TEMPLATE)
      continue;
    const symbolt *gsym = symbol_table.lookup(gid->identifier);
    if(gsym == nullptr || !gsym->type.get_bool(ID_is_template))
      continue;
    const cpp_declarationt &guide = to_cpp_declaration(gsym->type);
    if(
      guide.declarators().empty() ||
      !guide.declarators().front().get_bool("#is_deduction_guide"))
      continue;

    // The guide's parameter types are the deduction patterns.
    std::vector<typet> pattern_types;
    for(const auto &p :
        guide.declarators().front().type().find(ID_parameters).get_sub())
    {
      if(p.id() != ID_cpp_declaration)
        continue;
      const cpp_declarationt &pdecl =
        to_cpp_declaration(static_cast<const exprt &>(p));
      if(pdecl.declarators().empty())
        pattern_types.push_back(pdecl.type());
      else
        pattern_types.push_back(
          pdecl.declarators().front().merge_type(pdecl.type()));
    }
    if(pattern_types.size() != arg_types.size())
      continue;

    auto scope_it = cpp_scopes.id_map.find(gid->identifier);
    if(scope_it == cpp_scopes.id_map.end() || scope_it->second == nullptr)
      continue;

    std::optional<typet> guided;
    {
      // Deduce in the guide's own template scope, with a saved template map
      // so the caller's deduction state is left untouched.
      cpp_save_scopet save_scope(cpp_scopes);
      cpp_saved_template_mapt saved_map(template_map);
      cpp_scopes.go_to(*scope_it->second);
      template_map.build_unassigned(guide.template_type());

      cpp_typecheck_resolvet resolver(*this);
      bool deduced_ok = true;
      try
      {
        for(std::size_t i = 0; i < pattern_types.size(); ++i)
        {
          // e.g. libc++'s guide
          //   take_view(_Range&&, ...) -> take_view<all_t<_Range>>
          // deduces _Range = int(&)[1] from an array lvalue (the
          // forwarding-reference rule; all_t preserves the reference).
          resolver.guess_template_args(
            pattern_types[i],
            adjust_deduction_arg(
              pattern_types[i], arg_types[i], arg_is_lvalue[i]));
        }
      }
      catch(...)
      {
        deduced_ok = false;
      }

      if(
        deduced_ok && !template_map.build_template_args(guide.template_type())
                         .has_unassigned())
      {
        // Instantiate the guide's return type with the deduced parameters.
        typet ret = guide.type();
        try
        {
          typecheck_type(ret);
          guided = ret;
        }
        catch(...)
        {
        }
      }
    }

    if(guided.has_value() && guided->id() == ID_struct_tag)
      return guided;
  }

  // [over.match.class.deduct]/1 copy deduction candidate: when the
  // initializer is a single object whose type is (a reference to, possibly
  // cv-qualified) a specialization of this same class template, deduction
  // selects that very specialization -- `Box c{b}` with `b` of type
  // `Box<int>` is `Box<int>`, not `Box<Box<int>>`.
  if(arg_types.size() == 1)
  {
    typet at = arg_types.front();
    if(is_reference(at))
      at = to_reference_type(at).base_type();
    if(at.id() == ID_struct_tag)
    {
      const symbolt &arg_class = lookup(to_struct_tag_type(at));
      if(arg_class.base_name == class_template_name.get_base_name())
      {
        at.remove(ID_C_constant);
        return at;
      }
    }
  }

  // Implicit deduction guides synthesised from the primary template's
  // constructors ([over.match.class.deduct]/1.1, [temp.deduct.guide]): a
  // constructor C(P0, P1, ...) yields a guide that deduces the class template
  // parameters by matching the constructor parameter *patterns* against the
  // arguments.  This is needed whenever a constructor parameter is not exactly
  // a template parameter -- e.g. `Wrap(T *p)` must deduce `Wrap<int>` from an
  // `int *` argument, where the positional fallback would wrongly pick
  // `Wrap<int *>`.
  std::vector<typet> deduced_types;
  {
    const symbolt *csym = symbol_table.lookup(template_id->identifier);
    auto scope_it = cpp_scopes.id_map.find(template_id->identifier);
    if(
      csym != nullptr && csym->type.id() == ID_cpp_declaration &&
      csym->type.get_bool(ID_is_template) &&
      scope_it != cpp_scopes.id_map.end() && scope_it->second != nullptr)
    {
      const cpp_declarationt &cdecl = to_cpp_declaration(csym->type);
      for(const auto &mem : cdecl.type().find(ID_body).get_sub())
      {
        if(!deduced_types.empty())
          break;
        if(mem.id() != ID_cpp_declaration)
          continue;
        const cpp_declarationt &mdecl =
          to_cpp_declaration(static_cast<const exprt &>(mem));
        if(mdecl.type().id() != ID_constructor || mdecl.declarators().empty())
          continue;

        // Constructor parameter patterns (in terms of the class parameters).
        std::vector<typet> patterns;
        for(const auto &p :
            mdecl.declarators().front().type().find(ID_parameters).get_sub())
        {
          if(p.id() != ID_cpp_declaration)
            continue;
          const cpp_declarationt &pdecl =
            to_cpp_declaration(static_cast<const exprt &>(p));
          patterns.push_back(
            pdecl.declarators().empty()
              ? pdecl.type()
              : pdecl.declarators().front().merge_type(pdecl.type()));
        }
        if(patterns.empty() || patterns.size() != arg_types.size())
          continue;

        cpp_save_scopet save_scope(cpp_scopes);
        cpp_saved_template_mapt saved_map(template_map);
        cpp_scopes.go_to(*scope_it->second);
        template_map.build_unassigned(cdecl.template_type());

        cpp_typecheck_resolvet resolver(*this);
        bool deduced_ok = true;
        try
        {
          for(std::size_t i = 0; i < patterns.size(); ++i)
          {
            resolver.guess_template_args(
              patterns[i],
              adjust_deduction_arg(
                patterns[i], arg_types[i], arg_is_lvalue[i]));
          }
        }
        catch(...)
        {
          deduced_ok = false;
        }

        if(deduced_ok)
        {
          const cpp_template_args_tct ta =
            template_map.build_template_args(cdecl.template_type());
          if(!ta.has_unassigned())
          {
            std::vector<typet> dt;
            bool all_type_args = true;
            for(const auto &a : ta.arguments())
            {
              if(a.id() == ID_type)
                dt.push_back(a.type());
              else
              {
                all_type_args = false;
                break;
              }
            }
            if(all_type_args && !dt.empty())
              deduced_types = std::move(dt);
          }
        }
      }
    }
  }

  // Aggregate deduction candidate (N5008 [over.match.class.deduct]/1.8,
  // C++20): if the class has no constructors of its own, a hypothetical
  // guide is formed whose parameter types are the AGGREGATE ELEMENT
  // types; template arguments are deduced from the initializer per
  // [temp.deduct.call].  Deduce through the data members' declared
  // types, so a member of dependent-alias type (`range_difference_t<
  // _View>`, a non-deduced context) constrains nothing while the
  // plain `_View` member deduces with the /2 adjustments below (libc++
  // take_view's CTAD from `(__range, __n)`).
  if(deduced_types.empty())
  {
    const symbolt *csym = symbol_table.lookup(template_id->identifier);
    auto scope_it = cpp_scopes.id_map.find(template_id->identifier);
    if(
      csym != nullptr && csym->type.id() == ID_cpp_declaration &&
      csym->type.get_bool(ID_is_template) &&
      scope_it != cpp_scopes.id_map.end() && scope_it->second != nullptr)
    {
      const cpp_declarationt &cdecl = to_cpp_declaration(csym->type);
      bool has_ctor = false;
      std::vector<typet> member_patterns;
      for(const auto &mem : cdecl.type().find(ID_body).get_sub())
      {
        if(mem.id() != ID_cpp_declaration)
          continue;
        const cpp_declarationt &mdecl =
          to_cpp_declaration(static_cast<const exprt &>(mem));
        if(mdecl.type().id() == ID_constructor)
        {
          has_ctor = true;
          break;
        }
        if(mdecl.get_bool(ID_is_template) || mdecl.is_typedef())
          continue;
        if(mdecl.storage_spec().is_static())
          continue;
        for(const auto &d : mdecl.declarators())
        {
          if(d.type().id() == ID_function_type)
            continue; // member function, not an element
          member_patterns.push_back(d.merge_type(mdecl.type()));
        }
      }
      if(
        !has_ctor && !member_patterns.empty() &&
        arg_types.size() <= member_patterns.size())
      {
        // N5008 [temp.deduct.call]/2: for deduction against a by-value
        // parameter, an array argument decays to a pointer, a function
        // to a function pointer, and top-level cv-qualification is
        // dropped.
        std::vector<typet> adjusted_args = arg_types;
        for(auto &at : adjusted_args)
        {
          if(is_reference(at))
            at = to_reference_type(at).base_type();
          if(at.id() == ID_array)
            at = pointer_type(to_array_type(at).element_type());
          else if(at.id() == ID_code)
            at = pointer_type(at);
          at.remove(ID_C_constant);
        }
        cpp_save_scopet save_scope(cpp_scopes);
        cpp_saved_template_mapt saved_map(template_map);
        cpp_scopes.go_to(*scope_it->second);
        template_map.build_unassigned(cdecl.template_type());
        cpp_typecheck_resolvet resolver(*this);
        bool deduced_ok = true;
        try
        {
          for(std::size_t i = 0; i < adjusted_args.size(); ++i)
            resolver.guess_template_args(member_patterns[i], adjusted_args[i]);
        }
        catch(...)
        {
          deduced_ok = false;
        }
        if(deduced_ok)
        {
          const cpp_template_args_tct ta =
            template_map.build_template_args(cdecl.template_type());
          if(!ta.has_unassigned())
          {
            std::vector<typet> dt;
            bool all_type_args = true;
            for(const auto &a : ta.arguments())
            {
              if(a.id() == ID_type)
                dt.push_back(a.type());
              else
              {
                all_type_args = false;
                break;
              }
            }
            if(all_type_args && !dt.empty())
              deduced_types = std::move(dt);
          }
        }
      }
    }
  }

  // Positional fallback ([over.match.class.deduct], simplified) when no
  // constructor-pattern guide deduced the arguments:
  //  * a trailing parameter pack absorbs the remaining arguments, so the flat
  //    template-argument list is simply every argument type
  //    (`C<...Ts>{a, b}` -> `C<decltype(a), decltype(b)>`);
  //  * otherwise each type parameter takes one argument positionally
  //    (`Pair<A, B>{a, b}` -> `Pair<decltype(a), decltype(b)>`); a single
  //    parameter shared by several aggregate members (`Agg<T>{x, y}`) is fixed
  //    by the first argument, the rest being members of that same type.
  if(deduced_types.empty())
  {
    if(has_pack)
      deduced_types = arg_types;
    else
      for(std::size_t i = 0; i < n_type_params && i < arg_types.size(); ++i)
        deduced_types.push_back(arg_types[i]);
  }

  irept template_args(ID_template_args);
  irept &args_sub = template_args.add(ID_arguments);
  for(const auto &t : deduced_types)
  {
    exprt type_arg(ID_type);
    type_arg.type() = t;
    args_sub.get_sub().push_back(type_arg);
  }

  cpp_namet new_name = class_template_name;
  new_name.get_sub().push_back(template_args);
  typet result = static_cast<typet &>(static_cast<irept &>(new_name));
  typecheck_type(result);
  return result;
}

void cpp_typecheckt::convert(cpp_declarationt &declaration)
{
  // see if the declaration is empty
  if(declaration.is_empty())
    return;

  // C++20 abbreviated function templates: if a non-template function
  // has 'auto' parameters, synthesize template type parameters.
  if(!declaration.is_template())
  {
    for(auto &d : declaration.declarators())
    {
      irept &func_type = d.type();
      if(func_type.id() != ID_function_type)
        continue;

      irept &params = func_type.add(ID_parameters);
      unsigned auto_count = 0;

      for(auto &p : params.get_sub())
      {
        irept &param_type = p.add(ID_type);
        if(param_type.id() == ID_auto)
          ++auto_count;
      }

      if(auto_count == 0)
        continue;

      // Synthesize template type parameters
      template_typet tmpl;
      auto &tparams = tmpl.template_parameters();
      unsigned idx = 0;

      for(auto &p : params.get_sub())
      {
        irept &param_type = p.add(ID_type);
        if(param_type.id() != ID_auto)
          continue;

        std::string name = "_auto_T" + std::to_string(idx++);
        source_locationt loc =
          static_cast<const exprt &>(param_type).source_location();

        // Create template parameter declaration
        cpp_declarationt tparam_decl;
        tparam_decl.type() = typet("cpp-template-type");
        tparam_decl.set(ID_is_type, true);
        cpp_declaratort tparam_declarator;
        tparam_declarator.name() = cpp_namet(name, loc);
        tparam_decl.add_to_operands(std::move(tparam_declarator));
        tparams.push_back(static_cast<const template_parametert &>(
          static_cast<const exprt &>(tparam_decl)));

        // Replace auto with the synthesized type name
        cpp_namet type_name(name, loc);
        param_type =
          static_cast<const typet &>(static_cast<const irept &>(type_name));
      }

      declaration.set(ID_is_template, true);
      declaration.add(ID_template_type) = std::move(tmpl);
      break;
    }
  }

  // The function bodies must not be checked here,
  // but only at the very end when all declarations have been
  // processed (or considering forward declarations at least)

  // templates are done in a dedicated function
  if(declaration.is_template())
    convert_template_declaration(declaration);
  else
    convert_non_template_declaration(declaration);
}

codet cpp_typecheckt::convert_anonymous_union(cpp_declarationt &declaration)
{
  codet new_code(ID_decl_block);
  new_code.reserve_operands(declaration.declarators().size());

  // unnamed object
  std::string identifier="#anon_union"+std::to_string(anon_counter++);

  const cpp_namet cpp_name(identifier, declaration.source_location());
  cpp_declaratort declarator;
  declarator.name()=cpp_name;

  cpp_declarator_convertert cpp_declarator_converter(*this);

  const symbolt &symbol=
    cpp_declarator_converter.convert(declaration, declarator);

  if(!cpp_is_pod(declaration.type()))
  {
    const typet &followed =
      declaration.type().id() == ID_struct_tag
        ? static_cast<const typet &>(
            follow_tag(to_struct_tag_type(declaration.type())))
      : declaration.type().id() == ID_union_tag
        ? static_cast<const typet &>(
            follow_tag(to_union_tag_type(declaration.type())))
      : declaration.type().id() == ID_c_enum_tag
        ? static_cast<const typet &>(
            follow_tag(to_c_enum_tag_type(declaration.type())))
        : declaration.type();
    error().source_location = followed.source_location();
    error() << "anonymous union is not POD" << eom;
    throw 0;
  }

  new_code.add_to_operands(code_frontend_declt(cpp_symbol_expr(symbol)));

  // do scoping
  symbolt &union_symbol = symbol_table.get_writeable_ref(
    follow_tag(to_union_tag_type(symbol.type)).get(ID_name));

  for(const auto &c : to_union_type(union_symbol.type).components())
  {
    if(c.type().id() == ID_code)
    {
      error().source_location=union_symbol.type.source_location();
      error() << "anonymous union '" << union_symbol.base_name
              << "' shall not have function members" << eom;
      throw 0;
    }

    const irep_idt &base_name = c.get_base_name();

    if(cpp_scopes.current_scope().contains(base_name))
    {
      error().source_location=union_symbol.type.source_location();
      error() << "identifier '" << base_name << "' already in scope" << eom;
      throw 0;
    }

    cpp_idt &id=cpp_scopes.current_scope().insert(base_name);
    id.id_class = cpp_idt::id_classt::SYMBOL;
    id.identifier = c.get_name();
    id.class_identifier=union_symbol.name;
    id.is_member=true;
  }

  union_symbol.type.set(ID_C_unnamed_object, symbol.base_name);

  return new_code;
}

void cpp_typecheckt::convert_non_template_declaration(
  cpp_declarationt &declaration)
{
  PRECONDITION(!declaration.is_template());

  // we first check if this is a typedef
  typet &declaration_type=declaration.type();
  bool is_typedef=declaration.is_typedef();

  // the name anonymous tag types
  declaration.name_anon_struct_union();

  // do the type of the declaration
  // For out-of-class member definitions with trailing return types
  // (e.g., auto S::f() -> iterator), the return type name must be
  // resolved in the class scope. Defer type resolution when the
  // declaration type is an unresolved name and a declarator is qualified.
  bool defer_type = false;
  if(!declaration.declarators().empty() && declaration_type.id() == ID_cpp_name)
  {
    for(const auto &d : declaration.declarators())
    {
      if(to_cpp_name(d.name()).is_qualified())
      {
        defer_type = true;
        break;
      }
    }
  }

  if(
    !defer_type &&
    (declaration.declarators().empty() || !has_auto(declaration_type)))
  {
    // C++11 trailing return type with decltype referencing parameters:
    // put function parameters temporarily into scope so decltype can
    // resolve them.
    bool handled = false;
    if(
      declaration_type.id() == ID_decltype &&
      !declaration.declarators().empty())
    {
      const auto &d = declaration.declarators().front();
      if(d.type().id() == ID_function_type)
      {
        const irept &params = d.type().find(ID_parameters);
        if(params.get_sub().size() > 0)
        {
          cpp_save_scopet save_scope(cpp_scopes);
          for(const auto &p : params.get_sub())
          {
            const cpp_declarationt &pdecl =
              static_cast<const cpp_declarationt &>(p);
            if(pdecl.declarators().empty())
              continue;
            typet ptype = pdecl.type();
            typecheck_type(ptype);
            // Guard against malformed parameter declarators that
            // reach this path through template instantiation
            // (e.g., variadic pack expansions where the pack has
            // no declarator-name sub-elements yet).  Without this
            // guard, the `.front()` below dereferences a null
            // pointer and crashes with SIGSEGV.
            const auto &name_sub = pdecl.declarators().front().name().get_sub();
            if(name_sub.empty())
              continue;
            const irep_idt &pname = name_sub.front().get(ID_identifier);
            if(pname.empty())
              continue;
            const std::string sym_name =
              id2string(cpp_scopes.current_scope().prefix) + id2string(pname);
            auxiliary_symbolt psym;
            psym.name = sym_name;
            psym.base_name = pname;
            psym.type = ptype;
            psym.mode = ID_cpp;
            psym.is_parameter = true;
            if(
              symbol_table.symbols.find(sym_name) == symbol_table.symbols.end())
              symbol_table.insert(std::move(psym));
            else
            {
              // A temporary parameter symbol of this name persists from
              // an earlier instantiation of the same template scope (the
              // symbol-table entry is not removed when the scope is
              // restored).  Refresh its type with the parameter type as
              // resolved under the current template arguments, so the
              // trailing-return decltype is deduced against THIS
              // instantiation's parameters (e.g. const T vs T, which
              // select different cv-qualified member overloads).
              symbol_table.get_writeable_ref(sym_name).type = ptype;
            }
            const symbolt &inserted = symbol_table.lookup_ref(sym_name);
            cpp_idt &id = cpp_scopes.put_into_scope(inserted);
            id.id_class = cpp_idt::id_classt::SYMBOL;
          }
          typecheck_type(declaration_type);
          handled = true;
        }
      }
    }

    if(!handled)
    {
      // For typedefs, skip elaborate_class_template inside the resolver.
      // Elaboration of typedef'd template instances is deferred to usage,
      // as indicated by the !is_typedef check below.
      if(is_typedef)
      {
        skip_typechecking_elaborate = true;
        typecheck_type(declaration_type);
        skip_typechecking_elaborate = false;
      }
      else
      {
        // C++17 CTAD: if the type is a class template name without
        // template arguments, try to deduce from constructor arguments.
        bool ctad_done = false;
        if(
          declaration_type.id() == ID_cpp_name &&
          !declaration.declarators().empty())
        {
          const auto &declarator = declaration.declarators().front();
          const irept &init_args = declarator.find("init_args");
          const exprt &init = declarator.value();
          std::vector<exprt> ctad_args;
          if(init_args.get_sub().size() > 0)
          {
            for(const auto &a : init_args.get_sub())
              ctad_args.push_back(static_cast<const exprt &>(a));
          }
          else if(
            init.is_not_nil() && init.id() == ID_initializer_list &&
            !init.operands().empty())
          {
            for(const auto &a : init.operands())
              ctad_args.push_back(a);
          }
          else if(init.is_not_nil())
          {
            ctad_args.push_back(init);
          }
          if(!ctad_args.empty())
          {
            if(
              auto deduced = deduce_class_template_arguments(
                to_cpp_name(static_cast<const irept &>(declaration_type)),
                ctad_args))
            {
              declaration_type = *deduced;
              ctad_done = true;
            }
          }
        }
        if(!ctad_done)
          typecheck_type(declaration_type);
      }
    } // !handled
  }

  // Elaborate any class template instance _unless_ we do a typedef.
  // These are only elaborated on usage!
  if(!is_typedef)
    elaborate_class_template(declaration_type);

  // mark as 'already typechecked'
  if(!declaration.declarators().empty() && !defer_type)
    already_typechecked_typet::make_already_typechecked(declaration_type);

  // Special treatment for anonymous unions
  if(
    declaration.declarators().empty() &&
    ((declaration.type().id() == ID_struct_tag &&
      follow_tag(to_struct_tag_type(declaration.type()))
        .get_bool(ID_C_is_anonymous)) ||
     (declaration.type().id() == ID_union_tag &&
      follow_tag(to_union_tag_type(declaration.type()))
        .get_bool(ID_C_is_anonymous)) ||
     declaration.type().get_bool(ID_C_is_anonymous)))
  {
    if(declaration.type().id() != ID_union_tag)
    {
      error().source_location = declaration.type().source_location();
      error() << "top-level declaration does not declare anything"
              << eom;
      throw 0;
    }

    convert_anonymous_union(declaration);
  }

  // do the declarators (optional)
  for(auto &d : declaration.declarators())
  {
    // N5008 [dcl.ambig.res]/1: `T D(a, b, ...)` where every `a, b` could
    // syntactically be a parameter declaration parses as a FUNCTION
    // declaration -- but the ambiguity only exists when the names CAN be
    // types; when a name does not resolve to a type, the construct is a
    // variable with a parenthesized initializer.  The parser (which has
    // no name lookup) always produced the function interpretation at
    // non-statement scope, so `void *&child(__left_);` at namespace
    // scope became a bogus function declaration whose "parameter type"
    // `__left_` later failed conversion (libc++'s __tree
    // __insert_unique node linking).  Re-interpret here, where lookup
    // is available.
    if(
      d.type().id() == ID_function_type && d.value().is_nil() && !is_typedef &&
        !d.get_is_parameter() &&
        // N5008 [dcl.fct]/6: a cv-qualifier-seq in this position belongs
        // to a (member) function declarator only; a variable cannot have
        // one, so `... do_close(catalog) const` is unambiguously a
        // function.  (Read through a CONST reference: the non-const
        // accessor add()s an empty node, which is not nil.)
        [&]() -> bool
      {
        const irept &mq =
          static_cast<const cpp_declaratort &>(d).method_qualifier();
        return mq.is_nil() || mq.id().empty();
      }())
    {
      // N5008 [basic.lookup.unqual]/5: for a member declared OUTSIDE
      // its class (`void messages<char>::do_close(catalog);`), names
      // after the declarator-id are looked up in the member's class.
      // Resolve the qualified declarator's scope and perform the
      // can-it-be-a-type probes there; probing at namespace scope
      // missed class-scope (and inherited, [class.member.lookup])
      // typedefs like messages_base::catalog and mis-reinterpreted the
      // explicit-specialization DECLARATION as a void variable with a
      // parenthesized initializer (the libstdc++ <locale>/<regex>
      // `template <> void messages<char>::do_close(catalog) const;`
      // shape).
      cpp_save_scopet redisambig_scope_guard(cpp_scopes);
      {
        bool name_is_qualified = false;
        for(const auto &sub : d.name().get_sub())
          if(sub.id() == "::")
            name_is_qualified = true;
        if(name_is_qualified)
        {
          try
          {
            cpp_typecheck_resolvet scope_resolver(*this);
            irep_idt scope_base;
            cpp_template_args_non_tct scope_targs;
            cpp_scopet &member_scope =
              scope_resolver.resolve_scope(d.name(), scope_base, scope_targs);
            cpp_scopes.go_to(member_scope);
          }
          catch(...)
          {
            // scope unresolvable: keep probing at the current scope
          }
        }
      }
      const irept::subt &params = d.type().find(ID_parameters).get_sub();
      bool all_bare_nontype_names = !params.empty();
      for(const auto &param : params)
      {
        if(param.id() != ID_cpp_declaration)
        {
          all_bare_nontype_names = false;
          break;
        }
        const cpp_declarationt &pdecl =
          static_cast<const cpp_declarationt &>(param);
        // the ambiguous shape: a bare unqualified name with an empty
        // declarator
        if(
          pdecl.type().id() != ID_cpp_name ||
          to_cpp_name(pdecl.type()).is_qualified() ||
          to_cpp_name(pdecl.type()).has_template_args() ||
          pdecl.declarators().size() != 1 ||
          pdecl.declarators().front().name().is_not_nil())
        {
          all_bare_nontype_names = false;
          break;
        }
        // does the name resolve to a TYPE?  If it can, [dcl.ambig.res]/1
        // keeps the function interpretation.
        cpp_typecheck_resolvet resolver(*this);
        const exprt as_type = resolver.resolve(
          to_cpp_name(pdecl.type()),
          cpp_typecheck_resolvet::wantt::TYPE,
          cpp_typecheck_fargst(),
          false); // no exception on failure
        if(as_type.is_not_nil() && as_type.id() == ID_type)
        {
          all_bare_nontype_names = false;
          break;
        }
      }
      if(all_bare_nontype_names)
      {
        // variable with parenthesized initializer: the initializer
        // expressions are the (mis-parsed) parameter names
        exprt init_args(ID_initializer);
        for(const auto &param : params)
        {
          const cpp_declarationt &pdecl =
            static_cast<const cpp_declarationt &>(param);
          init_args.add_to_operands(static_cast<const exprt &>(
            static_cast<const irept &>(to_cpp_name(pdecl.type()))));
        }
        typet var_type = to_type_with_subtype(d.type()).subtype();
        d.type() = var_type;
        d.init_args().swap(init_args);
      }
    }

    // copy the declarator (we destroy the original)
    cpp_declaratort declarator=d;

    cpp_declarator_convertert cpp_declarator_converter(*this);

    cpp_declarator_converter.is_typedef=is_typedef;

    symbolt &symbol=cpp_declarator_converter.convert(
      declaration_type, declaration.storage_spec(),
      declaration.member_spec(), declarator);

    if(!symbol.is_type && !symbol.is_extern && symbol.type.id() == ID_empty)
    {
      error().source_location = symbol.location;
      error() << "void-typed symbol not permitted" << eom;
      throw 0;
    }

    // any template instance to remember?
    if(declaration.find(ID_C_template).is_not_nil())
    {
      symbol.type.set(ID_C_template, declaration.find(ID_C_template));
      symbol.type.set(
        ID_C_template_arguments,
        declaration.find(ID_C_template_arguments));
    }

    // replace declarator by symbol expression
    exprt tmp=cpp_symbol_expr(symbol);
    d.swap(tmp);

    // is there a constructor to be called for the declarator?
    if(symbol.is_lvalue &&
       declarator.init_args().has_operands())
    {
      auto constructor = cpp_constructor(
        symbol.location,
        cpp_symbol_expr(symbol),
        declarator.init_args().operands());

      if(constructor.has_value())
        symbol.value = constructor.value();
      else
        symbol.value = nil_exprt();
    }
    else if(
      symbol.is_static_lifetime && !symbol.is_extern && symbol.value.is_nil() &&
      !declarator.init_args().has_operands())
    {
      // A namespace-scope or static-storage object with no initializer is
      // default-initialized.  Its construction is emitted later during
      // static initialization with access control disabled, so verify
      // here -- at the point of declaration, where the enclosing scope is
      // the point of use -- that the selected default constructor is
      // accessible ([dcl.init], [class.access]).  Block-scope automatic
      // variables are checked at their declaration statement instead.
      check_default_constructor_access(
        symbol.type, symbol.location, &cpp_scopes.current_scope());
    }
  }
}

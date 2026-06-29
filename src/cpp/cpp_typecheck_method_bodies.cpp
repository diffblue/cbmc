#include <algorithm>
#include <functional>
#include <set>
/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifdef DEBUG
#endif

#include <util/message.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

/// Per N5008 [temp.variadic]/7: the instantiation of a pack expansion whose
/// pack(s) expand to zero elements produces an empty list.  When a function
/// (or member function) template is instantiated with an empty type pack, a
/// pack expansion appearing as a template argument in the body -- e.g.
/// `Tr<U...>` for an empty `U` -- must collapse to `Tr<>`.  Otherwise the
/// argument keeps the (now unbound) pack reference, the surrounding `cpp_name`
/// fails to resolve, and the expression is silently left un-typechecked (so a
/// constexpr body folds to a wrong value).
///
/// This removes such zero-length pack-expansion *arguments* from every
/// template-argument list in \p body.  An argument is removed only when its
/// pack expansion is at its own level (it carries `ID_ellipsis`) and refers to
/// an empty pack; an argument that merely *contains* an empty pack nested
/// inside (e.g. `Outer<U...>`, whose ellipsis sits on the inner argument) is
/// kept and recursed into so the inner expansion is collapsed in place.
///
/// Empty packs are those recorded with size zero in the current
/// `template_map` (non-empty packs have already had their name substituted and
/// their `...` removed by the caller).
void cpp_typecheckt::remove_empty_pack_expansion_args(exprt &body)
{
  if(template_map.pack_size_map.empty())
    return;

  std::set<std::string> ep_names;
  for(const auto &ps : template_map.pack_size_map)
  {
    if(ps.second != 0)
      continue;
    const std::string f = id2string(ps.first);
    auto p = f.rfind("::");
    ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
  }
  if(ep_names.empty())
    return;

  // Does \p n reference (anywhere) one of the empty packs?
  std::function<bool(const irept &)> refers_empty_pack =
    [&](const irept &n) -> bool
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
      if(refers_empty_pack(s))
        return true;
    for(const auto &ns : n.get_named_sub())
      if(refers_empty_pack(ns.second))
        return true;
    return false;
  };

  auto is_empty_pack_expansion = [&](const irept &a) -> bool
  {
    const bool is_expansion =
      a.get_bool(ID_ellipsis) || a.find(ID_type).get_bool(ID_ellipsis);
    return is_expansion && refers_empty_pack(a);
  };

  std::function<void(irept &)> strip = [&](irept &node)
  {
    if(node.id() == ID_template_args)
    {
      auto &args = node.add(ID_arguments).get_sub();
      args.erase(
        std::remove_if(args.begin(), args.end(), is_empty_pack_expansion),
        args.end());
    }
    for(auto &s : node.get_sub())
      strip(s);
    for(auto &ns : node.get_named_sub())
      strip(ns.second);
  };
  strip(static_cast<irept &>(body));
}

/// Drain the deferred method-body queue.
///
/// Standard mapping (N5008 [temp.point]/1, [temp.point]/8, [temp.inst]/5):
/// this is CBMC's approximation of the *point of instantiation* model.  A
/// referenced function-template specialization needs only its *declaration*
/// instantiated at the reference ([temp.inst]/1); its *definition* is
/// instantiated at the POI that "immediately follows the namespace scope
/// declaration or definition that refers to the specialization".  Running this
/// drain *after* the namespace-scope `convert` loop (see
/// `cpp_typecheckt::typecheck`), with `while(!method_bodies.empty())` so that
/// bodies queued while converting another body are processed in a later
/// iteration, gives those definitions a clean, top-level context -- effectively
/// a "POI at end of translation unit".  Both member-function-template *and*
/// free-function-template specializations reach this queue (the latter via
/// `convert_non_template_declaration` -> `cpp_declarator_convertert` ->
/// `add_method_body` for non-`auto` bodies); the only definitions converted
/// inline are `auto`-return and `constexpr` ones that must fold/deduce
/// eagerly.
///
/// OPEN ISSUE (see doc/architectural/cpp-frontend-review-2026-06-23-
/// instantiation-context.md, "Correction"): definition *deferral* works.  The
/// remaining "nested body conversion" degradation (e.g. the
/// `cpp11_derived_to_base_pack_call_in_body` KNOWNBUG) is in *call resolution*
/// performed while a body is being drained here: a derived-to-base
/// ([temp.deduct.call]/4.3) call whose callee has a trailing parameter pack is
/// dropped (the callee instance is left unbindable) for every enclosing body
/// except `main`'s -- an as-yet-unexplained `main`-specific exemption that is
/// the key clue for the real fix.
void cpp_typecheckt::typecheck_method_bodies()
{
  instantiation_stackt old_instantiation_stack;
  old_instantiation_stack.swap(instantiation_stack);

  // The bodies drained here are converted outside any constant-evaluation
  // context (see instantiating_deferred_body): a function-template call
  // resolved while converting one of them materialises a real instance, so a
  // directly-deduced type-internal parameter pack must be expanded to its
  // deduced arity ([temp.variadic]) rather than left for constant folding.
  const bool saved_deferred = instantiating_deferred_body;
  instantiating_deferred_body = true;
  struct restore_deferredt
  {
    cpp_typecheckt &ct;
    bool saved;
    ~restore_deferredt()
    {
      ct.instantiating_deferred_body = saved;
    }
  } restore_deferred{*this, saved_deferred};

  while(!method_bodies.empty())
  {
    // Dangerous not to take a copy here. We'll have to make sure that
    // convert is never called with the same symbol twice.
    method_bodyt &method_body = *method_bodies.begin();
    symbolt &method_symbol = *method_body.method_symbol;

    template_map.swap(method_body.template_map);
    instantiation_stack.swap(method_body.instantiation_stack);

    method_bodies.erase(method_bodies.begin());

    // Per [temp.variadic]/5: set pack_size_map for empty
    // variadic function template parameters.
    {
      const irept &c_tmpl = method_symbol.type.find(ID_C_template);
      if(c_tmpl.is_not_nil())
      {
        for(const auto &p :
            static_cast<const template_typet &>(c_tmpl).template_parameters())
        {
          if(p.get_bool(ID_ellipsis))
          {
            irep_idt pid = p.type().get(ID_identifier);
            if(
              !pid.empty() &&
              template_map.type_map.find(pid) == template_map.type_map.end())
              template_map.pack_size_map[pid] = 0;
          }
        }
      }
    }

    exprt &body=method_symbol.value;
    if(body.id() == ID_cpp_not_typechecked)
      continue;

    // Per [temp.inst]/1: restore function template map if this
    // is an instantiated member function template.
    if(method_symbol.type.find(irep_idt{"#fn_template_type"}).is_not_nil())
    {
      template_map.build(
        static_cast<const template_typet &>(
          method_symbol.type.find(irep_idt{"#fn_template_type"})),
        static_cast<const cpp_template_args_tct &>(
          method_symbol.type.find(irep_idt{"#fn_template_args"})));
    }

    // N5008 [temp.variadic]/5: expand the body / member-initializer uses of a
    // function parameter pack that typecheck_compound_declarator replicated
    // into N parameters `base$0..base$N-1`.  Each pack-expansion use `pat...`
    // (a list element carrying ID_ellipsis that mentions the pack `base`) is
    // replaced by N copies of `pat`, the k-th with `base` renamed to `base$k`
    // and the ellipsis removed.  This must run before the single-element
    // substitution below, which strips ID_ellipsis unconditionally.  Acts only
    // when a multi-element expansion was recorded, so single-element/empty
    // bodies are untouched.
    {
      const irept &eprec =
        method_symbol.type.find(irep_idt{"#expanded_param_packs"});
      if(eprec.is_not_nil() && !eprec.get_sub().empty())
      {
        std::map<irep_idt, std::size_t> pack_counts;
        for(const auto &e : eprec.get_sub())
          pack_counts[e.id()] = e.get_size_t(ID_size);

        // The recorded pack base (if any) that a pack-expansion pattern node
        // mentions.
        std::function<irep_idt(const irept &)> ref_base =
          [&](const irept &n) -> irep_idt
        {
          if(n.id() == ID_name && pack_counts.count(n.get(ID_identifier)))
            return n.get(ID_identifier);
          for(const auto &s : n.get_sub())
            if(irep_idt r = ref_base(s); !r.empty())
              return r;
          for(const auto &ns : n.get_named_sub())
            if(irep_idt r = ref_base(ns.second); !r.empty())
              return r;
          return irep_idt{};
        };

        std::function<void(irept &, const irep_idt &, const irep_idt &)>
          rename = [&](irept &n, const irep_idt &base, const irep_idt &repl)
        {
          if(n.id() == ID_name && n.get(ID_identifier) == base)
            n.set(ID_identifier, repl);
          for(auto &s : n.get_sub())
            rename(s, base, repl);
          for(auto &ns : n.get_named_sub())
            rename(ns.second, base, repl);
        };

        std::function<void(irept &)> expand = [&](irept &node)
        {
          const bool is_arg_list = node.id() == ID_arguments;
          irept::subt &sub = node.get_sub();
          irept::subt newsub;
          for(auto &child : sub)
          {
            // A pack-expansion use is detected either by a preserved
            // ID_ellipsis marker on the pattern (brace-init / member-init
            // contexts) or, in a function-call argument list -- where the
            // parser may drop the `...` -- by a *bare* reference to the pack
            // base name (a parameter pack may only legally appear in a pack
            // expansion, so a bare use of the base name is one).  The
            // bare-cpp_name restriction is essential: an argument that merely
            // *contains* the pack nested inside a larger expression -- e.g.
            // `fsum(rest...)` as the initializer expression of a member
            // initializer `sum(fsum(rest...))` -- is a *single* argument whose
            // own pack expansion sits on the inner call's argument (and carries
            // its own ID_ellipsis); expanding the outer argument per element
            // here would wrongly turn `sum(fsum(rest...))` into
            // `sum(fsum(rest$0), fsum(rest$1))`.  Such nested expansions are
            // reached by the recursion below and expanded at their own level.
            irep_idt base;
            if(
              child.get_bool(ID_ellipsis) ||
              (is_arg_list && child.id() == ID_cpp_name))
              base = ref_base(child);
            if(!base.empty())
            {
              const std::size_t n = pack_counts[base];
              for(std::size_t k = 0; k < n; ++k)
              {
                irept copy = child;
                copy.remove(ID_ellipsis);
                rename(copy, base, id2string(base) + "$" + std::to_string(k));
                expand(copy);
                newsub.push_back(copy);
              }
            }
            else
            {
              expand(child);
              newsub.push_back(child);
            }
          }
          sub.swap(newsub);
          for(auto &ns : node.get_named_sub())
            expand(ns.second);
        };
        expand(static_cast<irept &>(body));
      }
    }

    // Per [temp.variadic]/7: substitute non-empty pack parameter
    // names in the body with their actual types.
    if(!template_map.pack_args_map.empty())
    {
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        if(pa.second.empty())
          continue;
        const std::string full = id2string(pa.first);
        auto p = full.rfind("::");
        const std::string sn =
          p != std::string::npos ? full.substr(p + 2) : full;
        const typet &t = pa.second.front();
        if(t.id() == ID_struct_tag)
        {
          // Use the full struct_tag identifier; resolve_scope can find
          // it directly via id_map / symbol_table.  Naive string-based
          // stripping breaks for nested template types.
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
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          node.remove(ID_ellipsis);
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        subst(static_cast<irept &>(body));
      }
    }

    // Per [temp.variadic]/7: substitute non-empty pack parameter
    // names in the body with their actual types.
    if(!template_map.pack_args_map.empty())
    {
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        if(pa.second.empty())
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
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        subst(static_cast<irept &>(body));
      }
    }

    // Per [temp.variadic]/7: remove empty pack expansion
    // expressions from member initializers in the body.
    if(!template_map.pack_size_map.empty())
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
        std::function<bool(const irept &)> has_ep = [&](const irept &n) -> bool
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
          for(const auto &s : n.get_sub())
            if(has_ep(s))
              return true;
          for(const auto &ns : n.get_named_sub())
            if(has_ep(ns.second))
              return true;
          return false;
        };
        // Check member_initializers in the declarator (if present)
        irept &mi = method_symbol.value.add(ID_member_initializers);
        if(mi.is_not_nil())
        {
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

    // N5008 [temp.variadic]/5,7: expand the body uses of a *function
    // template's own* value parameter pack (e.g. the `ts` in
    // `template<class T, class... Ts> R f(T t, Ts... ts) { g(ts...); }`).
    // Unlike a class parameter pack -- whose body uses are expanded by the
    // `#expanded_param_packs` block above using the names that
    // typecheck_compound_declarator replicated -- a function template's own
    // pack is deduced per call and its body is drained here; for a member
    // function template that body is *not* otherwise expanded (a free function
    // template's body is expanded in instantiate_template / by the call
    // resolver), so a pack-expansion call argument such as `g(ts...)` keeps
    // its `...` and fails to resolve ("symbol 'ts' is unknown").
    //
    // Drive the expansion from the *instantiated function's actual
    // parameters*, which are authoritative:
    //   * a call argument carrying ID_ellipsis whose referenced name `S`
    //     matches a single parameter `S` is a single-element pack -> strip the
    //     ellipsis (`g(ts...)` -> `g(ts)`);
    //   * one whose referenced name matches replicated parameters `S$0..S$k`
    //     (N >= 2) expands to one argument per parameter, `S` renamed to `S$i`;
    //   * one whose referenced name matches *no* parameter is a pack that was
    //     deduced empty (N == 0) -> drop the argument ([temp.variadic]/7).
    // Acts only on function-template instances (a `#fn_template_type` whose
    // trailing template parameter is a pack), and only on arguments that still
    // carry `...` (class-pack and struct_tag uses had theirs removed above),
    // so other contexts are unaffected.
    {
      const irept &fnt = method_symbol.type.find(irep_idt{"#fn_template_type"});
      bool own_pack = false;
      if(fnt.is_not_nil())
      {
        const auto &tps =
          static_cast<const template_typet &>(fnt).template_parameters();
        if(!tps.empty() && tps.back().get_bool(ID_ellipsis))
          own_pack = true;
      }
      if(own_pack && method_symbol.type.id() == ID_code)
      {
        // Group the current parameters by short name: an exact name maps to
        // itself; a replicated `stem$idx` name is collected under `stem`.
        const auto short_name = [](const irep_idt &id) -> std::string
        {
          const std::string s = id2string(id);
          const auto p = s.rfind("::");
          return p != std::string::npos ? s.substr(p + 2) : s;
        };
        std::set<std::string> exact_params;
        std::map<std::string, std::map<std::size_t, std::string>> indexed;
        for(const auto &prm : to_code_type(method_symbol.type).parameters())
        {
          const std::string pn = short_name(prm.get_identifier());
          const auto dollar = pn.rfind('$');
          if(
            dollar != std::string::npos && dollar + 1 < pn.size() &&
            pn.find_first_not_of("0123456789", dollar + 1) == std::string::npos)
            indexed[pn.substr(0, dollar)][std::stoul(pn.substr(dollar + 1))] =
              pn;
          else
            exact_params.insert(pn);
        }

        // Rename every short name `from` to `to` within a node.
        std::function<void(irept &, const std::string &, const irep_idt &)>
          rename = [&](irept &n, const std::string &from, const irep_idt &to)
        {
          if(n.id() == ID_name && short_name(n.get(ID_identifier)) == from)
            n.set(ID_identifier, to);
          for(auto &s : n.get_sub())
            rename(s, from, to);
          for(auto &ns : n.get_named_sub())
            rename(ns.second, from, to);
        };

        // The pack stem a pattern references: the first short name (matching
        // an exact or replicated parameter) found anywhere in the argument.
        std::function<std::string(const irept &)> referenced_stem =
          [&](const irept &n) -> std::string
        {
          if(n.id() == ID_name)
          {
            const std::string s = short_name(n.get(ID_identifier));
            if(exact_params.count(s) || indexed.count(s))
              return s;
          }
          for(const auto &s : n.get_sub())
            if(std::string r = referenced_stem(s); !r.empty())
              return r;
          for(const auto &ns : n.get_named_sub())
            if(std::string r = referenced_stem(ns.second); !r.empty())
              return r;
          return std::string{};
        };

        std::function<void(irept &)> expand_own = [&](irept &node)
        {
          if(node.id() == ID_arguments)
          {
            irept::subt &args = node.get_sub();
            irept::subt out;
            for(auto &arg : args)
            {
              if(!arg.get_bool(ID_ellipsis))
              {
                expand_own(arg);
                out.push_back(arg);
                continue;
              }
              const std::string stem = referenced_stem(arg);
              if(stem.empty())
                continue; // empty pack: drop ([temp.variadic]/7)
              if(indexed.count(stem))
              {
                for(const auto &kv : indexed.at(stem))
                {
                  irept copy = arg;
                  copy.remove(ID_ellipsis);
                  rename(copy, stem, kv.second);
                  expand_own(copy);
                  out.push_back(copy);
                }
              }
              else
              {
                // single-element pack: strip the ellipsis, keep the name
                arg.remove(ID_ellipsis);
                expand_own(arg);
                out.push_back(arg);
              }
            }
            args.swap(out);
          }
          else
            for(auto &s : node.get_sub())
              expand_own(s);
          for(auto &ns : node.get_named_sub())
            expand_own(ns.second);
        };
        expand_own(static_cast<irept &>(body));
      }
    }

    // Per [temp.variadic]/7: drop zero-length pack expansions from the
    // template-argument lists in the body (e.g. `Tr<U...>` -> `Tr<>` for an
    // empty `U`).
    remove_empty_pack_expansion_args(body);

#ifdef DEBUG
    std::cout << "convert_method_body: " << method_symbol.name << '\n';
    std::cout << "  is_not_nil: " << body.is_not_nil() << '\n';
    std::cout << "  !is_zero: " << (!body.is_zero()) << '\n';
#endif
    if(body.is_not_nil() && body != 0)
    {
      // For template-instantiated methods and methods from system
      // headers, suppress error messages so that failures (e.g.,
      // unsupported standard library constructs) do not increment
      // the error count.
      bool suppress = !instantiation_stack.empty();
      if(!suppress)
      {
        const auto &loc = method_symbol.location;
        const std::string file = id2string(loc.get_file());
        // Only suppress for system headers (paths under /usr/include,
        // /usr/lib, etc.), not for all absolute paths.
        suppress = file.find("/include/") != std::string::npos ||
                   file.find("\\include\\") != std::string::npos ||
                   file.find("/usr/lib/") == 0 ||
                   file.find("/Applications/") == 0;
      }
      if(suppress)
      {
        // Save/restore error count instead of using null_handler.
        // The null_message_handlert causes template instantiations
        // inside the body to fail (e.g., _Deallocate<_New_alignof>)
        // because some code paths behave differently when the
        // message handler is null.
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        suppress_elaborate = false;
        try
        {
          convert_function(method_symbol);
        }
        catch(...)
        {
          // Type-checking failed — clear the partially-checked body
          // so the function is cleanly in the "no body" state.
          method_symbol.value.make_nil();
        }
        get_message_handler().set_message_count(
          messaget::M_ERROR, errors_before);
      }
      else
      {
        had_template_instantiation = false;
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        suppress_elaborate = false;
        try
        {
          convert_function(method_symbol);

          // C++14: update struct component type after auto return type
          // deduction.
          if(
            method_symbol.type.id() == ID_code &&
            has_auto(to_code_type(method_symbol.type).return_type()) == false)
          {
            const irep_idt &class_id = method_symbol.type.get(ID_C_member_name);
            if(!class_id.empty())
            {
              symbolt *class_sym = symbol_table.get_writeable(class_id);
              if(class_sym != nullptr)
              {
                struct_union_typet &struct_type =
                  to_struct_union_type(class_sym->type);
                for(auto &comp : struct_type.components())
                {
                  if(
                    comp.get_name() == method_symbol.name &&
                    comp.type().id() == ID_code &&
                    has_auto(to_code_type(comp.type()).return_type()))
                  {
                    to_code_type(comp.type()).return_type() =
                      to_code_type(method_symbol.type).return_type();
                    break;
                  }
                }
              }
            }
          }
        }
        catch(int)
        {
          // If the error originated from template instantiation
          // (e.g., unsupported STL constructs), suppress it rather
          // than failing the entire translation unit.
          if(had_template_instantiation)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            continue;
          }
          throw;
        }
      }
    }
  }

  // [temp.inst]/11: "an implementation shall not implicitly instantiate ...
  // a non-virtual member function ... unless such instantiation is required."
  // Members that are odr-used were already moved out of deferred_method_bodies
  // into method_bodies by the function-identifier hook as their referencing
  // bodies were type-checked above (constructors, destructors, virtual members
  // and operators are never deferred in the first place).  As a reachability
  // safety net -- covering references that appeared before a member was
  // deferred, or reference shapes that do not flow through that hook -- emit
  // any still-deferred member that is referenced by an already-converted body,
  // draining transitively, and re-scan to a fixpoint.  Members that no
  // converted body references are left uninstantiated, as the standard
  // requires; this is exactly what lets an unused, ill-formed member of a
  // specialization remain harmless ([temp.inst]/8, /11).
  std::function<void(const irept &, std::set<irep_idt> &)> gather_referenced =
    [&](const irept &n, std::set<irep_idt> &referenced)
  {
    if(n.id() == ID_symbol)
    {
      const irep_idt id = n.get(ID_identifier);
      if(!id.empty())
        referenced.insert(id);
    }
    for(const auto &s : n.get_sub())
      gather_referenced(s, referenced);
    for(const auto &ns : n.get_named_sub())
      gather_referenced(ns.second, referenced);
  };

  while(!deferred_method_bodies.empty())
  {
    std::set<irep_idt> referenced;
    for(const auto &s : symbol_table.symbols)
    {
      // Only converted (reachable) bodies count as references; a body still
      // parked in deferred_method_bodies is not itself instantiated, so its
      // references must not keep other members alive ([temp.inst]/11).
      if(
        s.second.type.id() == ID_code && s.second.value.is_not_nil() &&
        s.second.value.id() != ID_cpp_not_typechecked &&
        deferred_method_bodies.find(s.first) == deferred_method_bodies.end())
        gather_referenced(s.second.value, referenced);
    }

    std::vector<irep_idt> to_emit;

    // [class.dtor]/12: a destructor is *potentially invoked* when an object of
    // its class is created (e.g. at the end of a block or full-expression for
    // an automatic or temporary object).  Destructor calls for such objects
    // are synthesised later, during goto-conversion, so they are not visible
    // as references in the type-checked bodies scanned above.  Recover that
    // odr-use from the type system: a class's destructor is required exactly
    // when the class is constructed, i.e. when one of its constructors is
    // odr-used.  Collect the classes whose constructors are referenced.
    std::set<irep_idt> constructed_classes;
    for(const irep_idt &r : referenced)
    {
      const symbolt *rs = symbol_table.lookup(r);
      if(
        rs != nullptr && rs->type.id() == ID_code &&
        to_code_type(rs->type).return_type().id() == ID_constructor)
      {
        const irep_idt cls = rs->type.get(ID_C_member_name);
        if(!cls.empty())
          constructed_classes.insert(cls);
      }
    }

    for(const auto &d : deferred_method_bodies)
    {
      bool required = referenced.count(d.first) != 0;
      if(!required)
      {
        // Odr-used as a constructor member-initializer target.  A synthesized
        // (implicitly-defined or explicitly-defaulted) constructor lowers its
        // base/member subobject initializer to a class-name constructor call
        // that is resolved to the concrete overload only during goto
        // conversion, so the callee is not visible to the symbol-reference
        // scan above.  typecheck_member_initializer records the resolved
        // callee, so honour that here ([temp.inst]/4: an odr-used implicitly-
        // instantiated member must be instantiated).
        if(odr_used_by_member_initializer.count(d.first) != 0)
          required = true;
      }
      if(!required)
      {
        // A deferred destructor of a constructed class is potentially
        // invoked and must be instantiated ([class.dtor]/12, [temp.inst]/4).
        const symbolt *ds = symbol_table.lookup(d.first);
        if(
          ds != nullptr && ds->type.id() == ID_code &&
          to_code_type(ds->type).return_type().id() == ID_destructor &&
          constructed_classes.count(ds->type.get(ID_C_member_name)) != 0)
          required = true;
      }
      if(required)
        to_emit.push_back(d.first);
    }

    // Remaining deferred members are referenced by no converted body:
    // do not instantiate them ([temp.inst]/11).
    if(to_emit.empty())
      break;

    for(const auto &id : to_emit)
    {
      auto it = deferred_method_bodies.find(id);
      if(it != deferred_method_bodies.end())
      {
        method_bodies.push_back(std::move(it->second));
        deferred_method_bodies.erase(it);
      }
    }

    // Process the just-emitted members plus any methods added as side
    // effects.  The function-identifier hook may move further deferred
    // members into method_bodies here; the enclosing loop re-scans to a
    // fixpoint to pick up anything it misses.
    while(!method_bodies.empty())
    {
      method_bodyt &method_body = *method_bodies.begin();
      symbolt &method_symbol = *method_body.method_symbol;

      template_map.swap(method_body.template_map);
      instantiation_stack.swap(method_body.instantiation_stack);

      method_bodies.erase(method_bodies.begin());

      // Per [temp.variadic]/5: set pack_size_map for empty
      // variadic function template parameters.
      {
        const irept &c_tmpl = method_symbol.type.find(ID_C_template);
        if(c_tmpl.is_not_nil())
        {
          for(const auto &p :
              static_cast<const template_typet &>(c_tmpl).template_parameters())
          {
            if(p.get_bool(ID_ellipsis))
            {
              irep_idt pid = p.type().get(ID_identifier);
              if(
                !pid.empty() &&
                template_map.type_map.find(pid) == template_map.type_map.end())
                template_map.pack_size_map[pid] = 0;
            }
          }
        }
      }

      exprt &body = method_symbol.value;
      if(body.id() == ID_cpp_not_typechecked)
        continue;

      if(body.is_not_nil() && body != 0)
      {
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        try
        {
          convert_function(method_symbol);
        }
        catch(...)
        {
        }
        get_message_handler().set_message_count(
          messaget::M_ERROR, errors_before);
      }
    }
  }

  old_instantiation_stack.swap(instantiation_stack);
}

void cpp_typecheckt::add_method_body(symbolt *_method_symbol)
{
#ifdef DEBUG
  std::cout << "add_method_body: " << _method_symbol->name << '\n';
#endif
  // Converting a method body might add method bodies for methods that we have
  // already analyzed. Adding the same method more than once causes duplicated
  // symbol prefixes, therefore we have to keep track.
  if(methods_seen.insert(_method_symbol->name).second)
  {
    // If this method was deferred (its class is a template instance and
    // the method body wasn't type-checked during class instantiation),
    // the current template_map may not contain the class template
    // parameters. Build them from the class symbol so that names like
    // _Alloc inside the method body resolve correctly.
    template_mapt method_map = template_map;
    {
      const irep_idt &class_id = _method_symbol->type.get(ID_C_member_name);
      if(!class_id.empty())
      {
        const symbolt *class_sym = symbol_table.lookup(class_id);
        if(
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template).is_not_nil() &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil())
        {
          method_map.build(
            static_cast<const template_typet &>(
              class_sym->type.find(ID_C_template)),
            static_cast<const cpp_template_args_tct &>(
              class_sym->type.find(ID_C_template_arguments)));
        }
      }
    }
    bool defer = false;
    {
      const irep_idt &class_id = _method_symbol->type.get(ID_C_member_name);
      if(!class_id.empty())
      {
        const symbolt *class_sym = symbol_table.lookup(class_id);
        bool is_template_instance =
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil();
        if(is_template_instance)
        {
          // N5008 [temp.inst]/11: "an implementation shall not implicitly
          // instantiate ... a non-virtual member function ... unless such
          // instantiation is required."  Only *virtual* members are the
          // permitted-eager carve-out (second sentence of /11); every other
          // member -- ordinary methods, operators and the special members
          // (constructors, destructors, assignment) -- is deferred and pulled
          // in only when odr-used.  Constructor odr-use is visible as a call
          // in the type-checked body; destructor odr-use for automatic and
          // temporary objects is recovered in typecheck_method_bodies() from
          // the constructed-class set ([class.dtor]/12).
          bool is_virtual = _method_symbol->type.get_bool(ID_C_is_virtual);
          if(!is_virtual)
            defer = true;
        }
      }
    }

    if(defer)
    {
      deferred_method_bodies.emplace(
        _method_symbol->name,
        method_bodyt(_method_symbol, method_map, instantiation_stack));
    }
    else
    {
      method_bodies.push_back(
        method_bodyt(_method_symbol, method_map, instantiation_stack));
    }
  }
#ifdef DEBUG
  else
    std::cout << "  already exists\n";
#endif
}

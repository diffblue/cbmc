#include <algorithm>
#include <functional>
#include <optional>
#include <set>
/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifdef DEBUG
#endif

#include <util/arith_tools.h>
#include <util/c_types.h>
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
/// Shared preprocessing for a deferred method body about to be converted:
/// restore an instantiated member function template's template map
/// ([temp.inst]/1, from #fn_template_type / #fn_template_args), expand the
/// body's uses of replicated function parameter packs ([temp.variadic]/5)
/// and drop zero-length pack expansions ([temp.variadic]/7).  Used by BOTH
/// the main typecheck_method_bodies drain and the deferred-member fixpoint
/// drain; the latter previously skipped all of this, so a member function
/// template instance drained there (e.g. via the odr-use requeue) failed to
/// convert ("symbol '__args' is unknown") and was silently left bodyless.
void cpp_typecheckt::prepare_deferred_method_body(symbolt &method_symbol)
{
  exprt &body = method_symbol.value;

  // N5008 [temp.spec.partial.match]: for a member of a PARTIAL
  // specialization instance, the enclosing class's parameters were bound
  // by deduction against the argument pattern; replay the deduction-time
  // pack bindings persisted on the class symbol (#spec_template_packs),
  // non-overriding.  Without them a CLASS-level pack reference in the
  // body -- e.g. the `get<_Idx>()...` call-argument expansion in libc++
  // __perfect_forward's `operator()` -- has no binding at drain time,
  // and the fn-param-driven expansion below drops the argument as an
  // empty pack ([temp.variadic]/7 misapplied), silently truncating the
  // call.
  {
    const irep_idt &class_id = method_symbol.type.get(ID_C_member_name);
    const symbolt *class_sym =
      class_id.empty() ? nullptr : symbol_table.lookup(class_id);
    if(class_sym != nullptr)
    {
      const irept &bindings =
        class_sym->type.find(irep_idt{"#spec_template_packs"});
      for(const auto &entry : bindings.get_sub())
      {
        const irep_idt pid = entry.get(ID_identifier);
        if(pid.empty())
          continue;
        if(entry.id() == irep_idt{"pack_types"})
        {
          if(
            template_map.pack_size_map.find(pid) !=
            template_map.pack_size_map.end())
            continue;
          std::vector<typet> elems;
          for(const auto &t : entry.get_sub())
            elems.push_back(static_cast<const typet &>(t));
          template_map.pack_size_map[pid] = elems.size();
          if(!elems.empty())
          {
            if(elems.size() == 1)
              template_map.type_map.emplace(pid, elems.front());
            template_map.pack_args_map[pid] = std::move(elems);
          }
        }
        else if(entry.id() == irep_idt{"pack_exprs"})
        {
          if(
            template_map.pack_size_map.find(pid) !=
            template_map.pack_size_map.end())
            continue;
          std::vector<exprt> vals;
          for(const auto &v : entry.get_sub())
            vals.push_back(static_cast<const exprt &>(v));
          template_map.pack_size_map[pid] = vals.size();
          if(!vals.empty())
          {
            if(vals.size() == 1)
              template_map.expr_map.emplace(pid, vals.front());
            template_map.pack_expr_map[pid] = std::move(vals);
          }
        }
      }
    }
  }

  // Per [temp.inst]/1: restore function template map if this
  // is an instantiated member function template.
  if(method_symbol.type.find(irep_idt{"#fn_template_type"}).is_not_nil())
  {
    template_map.build(
      static_cast<const template_typet &>(
        method_symbol.type.find(irep_idt{"#fn_template_type"})),
      static_cast<const cpp_template_args_tct &>(
        method_symbol.type.find(irep_idt{"#fn_template_args"})));

    // N5008 [temp.variadic]/5,8: with MULTIPLE parameter packs the flat
    // #fn_template_args list cannot encode the split between the packs
    // (std::pair's piecewise delegation target, two type packs + two
    // non-type index packs).  Replay the deduction-time pack bindings
    // persisted by instantiate_template.
    const irept &packs =
      method_symbol.type.find(irep_idt{"#fn_template_packs"});
    for(const auto &entry : packs.get_sub())
    {
      const irep_idt pid = entry.get(ID_identifier);
      if(entry.id() == ID_expression)
      {
        std::vector<exprt> vals;
        for(const auto &v : entry.get_sub())
          vals.push_back(static_cast<const exprt &>(v));
        template_map.pack_size_map[pid] = vals.size();
        if(!vals.empty())
        {
          template_map.pack_expr_map[pid] = vals;
          template_map.expr_map[pid] = vals.front();
        }
        continue;
      }
      std::vector<typet> elems;
      for(const auto &t : entry.get_sub())
        elems.push_back(static_cast<const typet &>(t));
      template_map.pack_size_map[pid] = elems.size();
      template_map.pack_args_map[pid] = elems;
      if(!elems.empty())
        template_map.type_map[pid] = elems.front();
    }

    // N5008 [temp.variadic]/7: an expansion over an EMPTY pack produces an
    // empty list.  With the pack bindings replayed above, drop
    // member-initializer arguments that reference an empty pack outside
    // `sizeof...` (which is just 0, [temp.variadic]/8) -- e.g.
    // `second(std::forward<_Args2>(std::get<_Indexes2>(__tuple2))...)` in
    // std::pair's piecewise delegation target with _Args2/_Indexes2 empty
    // becomes `second()`.  Left in place, the unsubstitutable pack
    // reference fails the body's conversion and the member is dropped.
    if(!packs.get_sub().empty())
    {
      std::set<std::string> empty_pack_shorts;
      for(const auto &entry : packs.get_sub())
      {
        if(!entry.get_sub().empty())
          continue;
        const std::string f = id2string(entry.get(ID_identifier));
        auto p = f.rfind("::");
        empty_pack_shorts.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
      if(!empty_pack_shorts.empty())
      {
        std::function<bool(const irept &)> refs_ep = [&](const irept &n)
        {
          if(n.get_bool("#sizeof_pack"))
            return false;
          if(
            n.id() == ID_name &&
            empty_pack_shorts.count(id2string(n.get(ID_identifier))))
            return true;
          for(const auto &sn : n.get_sub())
            if(refs_ep(sn))
              return true;
          for(const auto &ns : n.get_named_sub())
            if(refs_ep(ns.second))
              return true;
          return false;
        };
        std::function<void(irept &)> drop = [&](irept &n)
        {
          if(n.id() == ID_code && n.get(ID_statement) == ID_member_initializer)
          {
            irept::subt &args = n.get_sub();
            args.erase(
              std::remove_if(
                args.begin(),
                args.end(),
                [&](const irept &a) { return refs_ep(a); }),
              args.end());
            return;
          }
          for(auto &sn : n.get_sub())
            drop(sn);
          for(auto &ns : n.get_named_sub())
            drop(ns.second);
        };
        drop(static_cast<irept &>(body));
      }
    }

    // N5008 [temp.variadic]/5: expand the remaining (non-empty)
    // pack-expansion mem-initializer arguments with the replayed pack
    // bindings -- `first(std::forward<_Args1>(std::get<_Indexes1>(
    // __tuple1))...)` in std::pair's piecewise delegation target mixes
    // a reference-type pack with a non-type index pack, which the
    // scalar convenience entries alone cannot expand; the unexpanded
    // ellipsis failed the body's conversion and the member was
    // dropped (std::map's piecewise-constructed key was havocked).
    expand_member_initializer_packs_in_body(
      static_cast<irept &>(body),
      template_map.pack_args_map,
      template_map.pack_expr_map);
  }

  // N5008 [expr.prim.fold]/1-3: reduce a fold expression over this member
  // function template's parameter pack.  The free-function-template body
  // expander in cpp_instantiate_template already handles folds; a MEMBER
  // function template body is prepared here instead, so without this the
  // fold's bare pack reference (e.g. `a` in `(a + ...)`) is left
  // unexpanded, fails to resolve, and the whole body is dropped ("no body
  // for callee").  A unary right fold `(pat op ...)` over an N-element pack
  // becomes the right-associated tree `pat0 op (pat1 op ... op patN-1)`; a
  // unary left fold `(... op pat)` the left-associated tree
  // `((pat0 op pat1) op ...) op patN-1`; a binary fold `(init op ... op pat)`
  // is a left fold seeded by `init` ([expr.prim.fold]/2).  An empty pack
  // yields the operator identity ([expr.prim.fold]/3: && -> true,
  // || -> false, comma -> void(), approximated as 0); a single element
  // yields the sole substituted pattern.  Runs for every arity (0, 1, N),
  // independent of the pack-count-driven expansion below.
  {
    // For an N>=2 pack, typecheck_compound_declarator replicated the pack
    // parameter into `base$0..base$N-1`; recover N per base from those
    // names.  (#expanded_param_packs records the same when present.)
    std::map<irep_idt, std::size_t> dollar_counts;
    const irept &eprec_f =
      method_symbol.type.find(irep_idt{"#expanded_param_packs"});
    if(eprec_f.is_not_nil() && !eprec_f.get_sub().empty())
    {
      for(const auto &e : eprec_f.get_sub())
        if(e.get_size_t(ID_size) >= 2)
          dollar_counts[e.id()] = e.get_size_t(ID_size);
    }
    if(method_symbol.type.id() == ID_code)
    {
      std::map<irep_idt, std::size_t> scan;
      for(const auto &p : to_code_type(method_symbol.type).parameters())
      {
        const std::string bn = id2string(p.get_base_name());
        const auto dollar = bn.rfind('$');
        if(dollar == std::string::npos || dollar + 1 >= bn.size())
          continue;
        if(bn.find_first_not_of("0123456789", dollar + 1) != std::string::npos)
          continue;
        ++scan[irep_idt{bn.substr(0, dollar)}];
      }
      for(const auto &c : scan)
        if(c.second >= 2)
          dollar_counts[c.first] = c.second;
    }

    // For an empty (0) or single-element (1) pack no `base$k` parameters are
    // produced (the sole element keeps the plain name `base`; an empty pack
    // leaves no parameter at all), so the element count is taken from the
    // instantiated pack size recorded in template_map.  When the member
    // template has exactly one parameter pack this is unambiguous.
    bool have_low_size = template_map.pack_size_map.size() == 1;
    std::size_t low_size =
      have_low_size ? template_map.pack_size_map.begin()->second : 0;
    if(have_low_size && low_size >= 2)
      have_low_size = false; // an N>=2 pack is handled via base$k above

    // The base name (renamed to base$k) that a fold pattern references, if
    // this member replicated an N>=2 pack.
    std::function<irep_idt(const irept &)> fold_ref_base =
      [&](const irept &n) -> irep_idt
    {
      if(n.id() == ID_name && dollar_counts.count(n.get(ID_identifier)))
        return n.get(ID_identifier);
      for(const auto &s : n.get_sub())
        if(irep_idt r = fold_ref_base(s); !r.empty())
          return r;
      for(const auto &ns : n.get_named_sub())
        if(irep_idt r = fold_ref_base(ns.second); !r.empty())
          return r;
      return irep_idt{};
    };
    std::function<void(irept &, const irep_idt &, const irep_idt &)>
      fold_rename = [&](irept &n, const irep_idt &base, const irep_idt &repl)
    {
      if(n.id() == ID_name && n.get(ID_identifier) == base)
        n.set(ID_identifier, repl);
      for(auto &s : n.get_sub())
        fold_rename(s, base, repl);
      for(auto &ns : n.get_named_sub())
        fold_rename(ns.second, base, repl);
    };

    auto identity_for = [](const irep_idt &fold_op) -> exprt
    {
      // [expr.prim.fold]/3: empty-pack unary fold values.  Only &&, ||, and
      // comma have a defined identity; comma yields void(), approximated
      // here (as in the free-function expander) by 0.
      if(fold_op == ID_and)
        return true_exprt{};
      if(fold_op == ID_or)
        return false_exprt{};
      return from_integer(0, signed_int_type());
    };

    std::function<void(irept &)> reduce_folds = [&](irept &node)
    {
      const bool is_right = node.id() == irep_idt("cpp_right_fold");
      const bool is_left = node.id() == irep_idt("cpp_left_fold");
      const bool is_binary = node.id() == irep_idt("cpp_binary_fold");
      const irept *pattern = nullptr;
      irept init_expr;
      if((is_right || is_left) && !node.get_sub().empty())
        pattern = &node.get_sub().front();
      else if(is_binary && node.get_sub().size() >= 2)
      {
        init_expr = node.get_sub()[0];
        pattern = &node.get_sub()[1];
      }
      if(pattern != nullptr)
      {
        const irep_idt fold_op = node.get(irep_idt("fold_op"));
        const irept pat = *pattern;
        const irep_idt base = fold_ref_base(pat);
        if(!base.empty())
        {
          // N>=2: build the associated tree over base$0..base$N-1.
          const std::size_t n = dollar_counts[base];
          auto elem = [&](std::size_t k) -> irept
          {
            irept c = pat;
            fold_rename(c, base, id2string(base) + "$" + std::to_string(k));
            reduce_folds(c);
            return c;
          };
          if(is_binary)
          {
            reduce_folds(init_expr);
            irept result = init_expr; // (((init op e0) op e1) op ...)
            for(std::size_t k = 0; k < n; ++k)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(result);
              bin.get_sub().push_back(elem(k));
              result = bin;
            }
            node = result;
          }
          else if(is_left)
          {
            irept result = elem(0); // ((e0 op e1) op ...) op eN-1
            for(std::size_t k = 1; k < n; ++k)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(result);
              bin.get_sub().push_back(elem(k));
              result = bin;
            }
            node = result;
          }
          else // right fold: e0 op (e1 op (... op eN-1))
          {
            irept result = elem(n - 1);
            for(int k = static_cast<int>(n) - 2; k >= 0; --k)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(elem(static_cast<std::size_t>(k)));
              bin.get_sub().push_back(result);
              result = bin;
            }
            node = result;
          }
          return;
        }
        // N5008 [temp.variadic]/5: a SINGLE-element function parameter pack
        // keeps its plain parameter name (no `base$k` replication), so a
        // fold whose pattern references exactly one of this method's own
        // parameters is a one-element fold regardless of how many OTHER
        // packs (e.g. the enclosing class template's) are in the map --
        // the pack_size_map.size()==1 gate below is only needed for the
        // EMPTY pack, where no parameter is left to witness the fold's
        // pack.
        bool single_by_param = false;
        if(method_symbol.type.id() == ID_code)
        {
          std::function<irep_idt(const irept &)> any_name =
            [&](const irept &n) -> irep_idt
          {
            if(n.id() == ID_name && !n.get(ID_identifier).empty())
              return n.get(ID_identifier);
            for(const auto &sn : n.get_sub())
              if(irep_idt r = any_name(sn); !r.empty())
                return r;
            for(const auto &ns : n.get_named_sub())
              if(irep_idt r = any_name(ns.second); !r.empty())
                return r;
            return irep_idt{};
          };
          const irep_idt pattern_name = any_name(pat);
          if(!pattern_name.empty())
          {
            std::size_t matches = 0;
            for(const auto &p : to_code_type(method_symbol.type).parameters())
              if(p.get_base_name() == pattern_name)
                ++matches;
            single_by_param = matches == 1;
          }
        }
        if(single_by_param || have_low_size)
        {
          const std::size_t n_elems =
            single_by_param ? std::size_t{1} : low_size;
          // Empty (0) or single (1) element: the pattern already references
          // the pack element by its plain name (or none, for 0), so no
          // renaming is needed.
          irept single = pat;
          reduce_folds(single);
          if(is_binary)
          {
            reduce_folds(init_expr);
            if(n_elems == 0)
              node = init_expr; // (init op ...) with empty pack -> init
            else
            {
              irept bin(fold_op); // (init op e0)
              bin.get_sub().push_back(init_expr);
              bin.get_sub().push_back(single);
              node = bin;
            }
          }
          else if(n_elems == 0)
            node = identity_for(fold_op);
          else
            node = single; // single element -> the pattern itself
          return;
        }
      }
      for(auto &s : node.get_sub())
        reduce_folds(s);
      for(auto &ns : node.get_named_sub())
        reduce_folds(ns.second);
    };
    if(
      !dollar_counts.empty() || have_low_size ||
      (method_symbol.type.id() == ID_code &&
       !to_code_type(method_symbol.type).parameters().empty()))
    {
      reduce_folds(static_cast<irept &>(body));
    }
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
    std::map<irep_idt, std::size_t> pack_counts;
    if(eprec.is_not_nil() && !eprec.get_sub().empty())
    {
      for(const auto &e : eprec.get_sub())
        pack_counts[e.id()] = e.get_size_t(ID_size);
    }
    else if(method_symbol.type.id() == ID_code)
    {
      // N5008 [temp.variadic]/5: when a member of a class template partial
      // specialization `C<R(A...)>` is instantiated, the member's parameter
      // pack `A... a` is expanded into distinct parameters `a$0..a$k` by
      // `template_mapt` during instantiation, which -- unlike the in-class
      // `compound_type` path -- does not leave an `#expanded_param_packs`
      // record.  Recover the per-pack counts from the already-expanded
      // parameter names so the body's pack-expansion uses (`a...`, e.g. the
      // libstdc++ `function<R(A...)>::operator()` body
      // `_M_invoker(_M_functor, std::forward<A>(__args)...)`) expand to the
      // full arity instead of collapsing to one argument.  A replicated
      // parameter is named `base$k`; group by base and count.
      std::map<irep_idt, std::size_t> counts;
      for(const auto &p : to_code_type(method_symbol.type).parameters())
      {
        const std::string bn = id2string(p.get_base_name());
        const auto dollar = bn.rfind('$');
        if(dollar == std::string::npos || dollar + 1 >= bn.size())
          continue;
        if(bn.find_first_not_of("0123456789", dollar + 1) != std::string::npos)
          continue;
        ++counts[irep_idt{bn.substr(0, dollar)}];
      }
      // Only treat as a pack expansion when more than one element was
      // produced; a single `base$0` is an ordinary case handled by the
      // single-element substitution below.
      for(const auto &c : counts)
        if(c.second >= 2)
          pack_counts[c.first] = c.second;
    }
    if(!pack_counts.empty())
    {
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

      std::function<void(irept &, const irep_idt &, const irep_idt &)> rename =
        [&](irept &n, const irep_idt &base, const irep_idt &repl)
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
              // N5008 [temp.variadic]/5: the k-th element of the expansion
              // substitutes the k-th element of EVERY pack the pattern
              // references.  Besides the function-parameter pack renamed
              // above, a bare reference to a deduced TEMPLATE type pack --
              // e.g. the explicit argument in `forward<A>(a)...` -- must
              // become that pack's k-th deduced type; leaving the whole
              // pack name in place makes the per-element call unresolvable
              // (deduction fails for every `forward` overload and the
              // enclosing body is dropped, the _Rb_tree
              // _M_emplace_hint_unique shape).
              std::function<void(irept &)> subst_type_pack = [&](irept &t)
              {
                if(
                  t.id() == ID_cpp_name && t.get_sub().size() == 1 &&
                  t.get_sub().front().id() == ID_name)
                {
                  const std::string nm =
                    id2string(t.get_sub().front().get(ID_identifier));
                  const auto p = nm.rfind("::");
                  const std::string suf =
                    p != std::string::npos ? nm.substr(p + 2) : nm;
                  for(const auto &pe : template_map.pack_args_map)
                  {
                    const std::string key = id2string(pe.first);
                    const auto q = key.rfind("::");
                    const std::string ksuf =
                      q != std::string::npos ? key.substr(q + 2) : key;
                    if(ksuf == suf && pe.second.size() == n && k < n)
                    {
                      t = pe.second[k];
                      return;
                    }
                  }
                }
                for(auto &s : t.get_sub())
                  subst_type_pack(s);
                for(auto &ns : t.get_named_sub())
                  subst_type_pack(ns.second);
              };
              subst_type_pack(copy);
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

  // N5008 [temp.variadic]/5: expand a call-argument pack expansion in the
  // body (e.g. `add(I...)` over a non-type parameter pack) to one argument
  // per element, substituting the pack's element value.  The in-class /
  // decltype paths use expand_call_argument_packs already; a function
  // template body reaches here without it, so a non-type pack call-argument
  // expansion would otherwise be left unexpanded.  Gated on a NON-type pack
  // being present (pack_expr_map): a body with only type / function-parameter
  // packs is already handled by the expansion above, and re-running the
  // call-argument expander over it would double-expand a function parameter
  // pack.
  if(!template_map.pack_expr_map.empty())
    template_map.expand_call_argument_packs(static_cast<irept &>(body));

  // Per [temp.variadic]/7: substitute non-empty pack parameter
  // names in the body with their actual types.
  if(!template_map.pack_args_map.empty())
  {
    std::map<std::string, irep_idt> pack_subst;
    for(const auto &pa : template_map.pack_args_map)
    {
      // N5008 [temp.variadic]/5: single-element packs only -- a
      // >=2-element pack whose name still appears here is a pattern the
      // per-element expander above substitutes in lockstep; stamping the
      // front element would concretize every expansion copy to element 0
      // (the _Hashtable _Scoped_node mem-init shape).
      if(pa.second.size() != 1)
        continue;
      const std::string full = id2string(pa.first);
      auto p = full.rfind("::");
      const std::string sn = p != std::string::npos ? full.substr(p + 2) : full;
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
        // N5008 [expr.sizeof]/5 + [temp.variadic]/8: `sizeof...(P)` is
        // a pack-size QUERY; stamping the single element's tag rewrote
        // it into the element type's BYTE size (the tuple
        // converting-element silent constructor drop).
        if(node.get_bool("#sizeof_pack"))
          return;
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
      // N5008 [temp.variadic]/5: single-element packs only -- a
      // >=2-element pack whose name still appears here is a pattern the
      // per-element expander above substitutes in lockstep; stamping the
      // front element would concretize every expansion copy to element 0
      // (the _Hashtable _Scoped_node mem-init shape).
      if(pa.second.size() != 1)
        continue;
      const std::string full = id2string(pa.first);
      auto p = full.rfind("::");
      const std::string sn = p != std::string::npos ? full.substr(p + 2) : full;
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
        // see above: keep `sizeof...(P)` operands intact
        // ([expr.sizeof]/5)
        if(node.get_bool("#sizeof_pack"))
          return;
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
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
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
          indexed[pn.substr(0, dollar)][std::stoul(pn.substr(dollar + 1))] = pn;
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
        // A mem-initializer stores its arguments as positional subs of the
        // member_initializer code node (no ID_arguments child): the same
        // [temp.variadic]/5 expansion applies -- the function parameter
        // pack in `__bound_args_(__bound_args...)` (libc++
        // __perfect_forward's constructor) must replicate to
        // `__bound_args$0..$k`.  Only ellipsis-carrying arguments are
        // touched, so the member-name sub is unaffected.
        if(
          node.id() == ID_arguments ||
          (node.id() == ID_code &&
           node.get(ID_statement) == ID_member_initializer))
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
            {
              // No stem matches this instance's parameters.  Drop the
              // expansion ONLY when a known-EMPTY pack governs it
              // ([temp.variadic]/7); an expansion whose pack is not
              // deducible from the parameter list HERE (e.g. `__u...` in
              // a delegating mem-initializer processed before the pack
              // parameters are replicated) must be left for the later
              // instantiation-time expansion -- dropping it truncated
              // the __tuple_impl delegation's argument list and the
              // constructor stopped resolving ([temp.variadic]/5:
              // lengths come from the packs expanded in the pattern).
              bool governed_by_empty = false;
              for(const auto &ps : template_map.pack_size_map)
              {
                if(ps.second != 0)
                  continue;
                const std::string key = id2string(ps.first);
                const auto q = key.rfind("::");
                const std::string suf =
                  q != std::string::npos ? key.substr(q + 2) : key;
                std::function<bool(const irept &)> names = [&](const irept &n)
                {
                  if(
                    n.id() == ID_name && id2string(n.get(ID_identifier)) == suf)
                    return true;
                  for(const auto &sn : n.get_sub())
                    if(names(sn))
                      return true;
                  for(const auto &ns : n.get_named_sub())
                    if(names(ns.second))
                      return true;
                  return false;
                };
                if(names(arg))
                {
                  governed_by_empty = true;
                  break;
                }
              }
              if(governed_by_empty)
                continue; // zero-length expansion: drop
              // The pack parameter may not be REPLICATED yet in this
              // instance's parameter list (path-dependent ordering
              // between parameter replication and mem-init expansion).
              // If the fn template's own trailing pack has a recorded
              // size k >= 1, replicate the argument by pack size,
              // renaming the value reference `name` -> `name$i`
              // ([temp.variadic]/5: one element per pack element; the
              // replicated parameter naming matches
              // expand_parameter_packs' `base$k` convention).
              {
                const irept &fnt2 =
                  method_symbol.type.find(irep_idt{"#fn_template_type"});
                std::size_t pack_sz = 0;
                bool have_sz = false;
                if(fnt2.is_not_nil())
                {
                  const auto &tps2 = static_cast<const template_typet &>(fnt2)
                                       .template_parameters();
                  if(!tps2.empty() && tps2.back().get_bool(ID_ellipsis))
                  {
                    const irep_idt pid2 =
                      tps2.back().id() == ID_type
                        ? tps2.back().type().get(ID_identifier)
                        : tps2.back().get(ID_identifier);
                    const auto it2 = template_map.pack_size_map.find(pid2);
                    if(it2 != template_map.pack_size_map.end())
                    {
                      pack_sz = it2->second;
                      have_sz = true;
                    }
                  }
                }
                // the VALUE name referenced by the pattern
                std::function<std::string(const irept &)> first_name =
                  [&](const irept &n) -> std::string
                {
                  if(n.id() == ID_name)
                    return id2string(n.get(ID_identifier));
                  for(const auto &sn : n.get_sub())
                  {
                    const std::string r = first_name(sn);
                    if(!r.empty())
                      return r;
                  }
                  for(const auto &ns : n.get_named_sub())
                  {
                    const std::string r = first_name(ns.second);
                    if(!r.empty())
                      return r;
                  }
                  return std::string{};
                };
                const std::string vname = first_name(arg);
                if(have_sz && !vname.empty())
                {
                  for(std::size_t k = 0; k < pack_sz; ++k)
                  {
                    irept copy = arg;
                    copy.remove(ID_ellipsis);
                    rename(copy, vname, vname + "$" + std::to_string(k));
                    out.push_back(copy);
                  }
                  continue;
                }
              }
              out.push_back(arg);
              continue; // keep for the later expansion pass
            }
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
}

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

    prepare_deferred_method_body(method_symbol);
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
          // The body is now properly type-checked: it must not be
          // nil'd by clean_up's deferred-members sweep.  A member
          // instantiated out of line re-enters deferred_typechecking
          // when its declarator is converted in a template scope
          // (typecheck_compound_declarator), so erase it here.
          deferred_typechecking.erase(method_symbol.name);
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
          // see the matching erase in the template-instantiation branch
          deferred_typechecking.erase(method_symbol.name);

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
          // N5008 [temp.deduct]/8: an UNRECOVERED "no viable function" failure
          // in this ordinary body (a call whose only candidates were function
          // templates all removed by substitution failures) must be diagnosed,
          // not silently swallowed.  pending_no_viable_call is set iff such a
          // failure's throw reached here without any intervening (recovering)
          // resolution, so it takes precedence over the unsupported-STL
          // leniency below.
          if(pending_no_viable_call)
          {
            error().source_location = pending_no_viable_location;
            error() << "found no match for symbol '"
                    << pending_no_viable_base_name << "'" << messaget::eom;
            pending_no_viable_call = false;
            method_symbol.value.make_nil();
            continue;
          }
          // N5008: not standards-conformant, but a pragmatic tolerance for
          // constructs the C++ front-end cannot yet fully model (complex STL
          // template metaprogramming, intrinsics, ...).  Rather than fail the
          // whole translation unit, this suppresses the error and keeps going.
          // Emit a warning so the resulting incomplete verification is
          // AUDITABLE rather than silently masked (this leniency has hidden
          // real front-end gaps -- e.g. std::initializer_list, std::variant,
          // std::expected, ranges, concepts and NTTP support that CBMC does not
          // actually model; such uses pass only vacuously).
          if(had_template_instantiation)
          {
            warning().source_location = method_symbol.location;
            warning()
              << "C++ front-end could not fully type-check '"
              << method_symbol.base_name
              << "' (unsupported construct); its body is left incomplete, so "
              << "verification involving it may be unsound" << messaget::eom;
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

      // [temp.inst]/1 + [temp.variadic]/5,7: identical preprocessing to the
      // main drain above -- restore the function-template map and expand the
      // replicated parameter-pack uses.  A member function template instance
      // drained here (e.g. requeued by the member-initializer odr-use
      // tracking) previously skipped this and failed to convert, silently
      // losing its body.
      prepare_deferred_method_body(method_symbol);

      if(body.is_not_nil() && body != 0)
      {
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        try
        {
          convert_function(method_symbol);
          // see the matching erase in typecheck_method_bodies
          deferred_typechecking.erase(method_symbol.name);
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

bool cpp_typecheckt::convert_deferred_method_now(const irep_idt &identifier)
{
  if(functions_being_typechecked.count(identifier) != 0)
    return false;

  // find the queued entry (lazy map first, then the drain queue)
  std::optional<method_bodyt> entry;
  auto d_it = deferred_method_bodies.find(identifier);
  if(d_it != deferred_method_bodies.end())
  {
    entry = std::move(d_it->second);
    deferred_method_bodies.erase(d_it);
  }
  else
  {
    for(auto it = method_bodies.begin(); it != method_bodies.end(); ++it)
    {
      if(it->method_symbol->name == identifier)
      {
        entry = std::move(*it);
        method_bodies.erase(it);
        break;
      }
    }
  }
  if(!entry.has_value())
    return false;

  symbolt *method_symbol = entry->method_symbol;
  if(method_symbol == nullptr || method_symbol->value.is_not_nil())
    return false;

  // Convert under the entry's recorded template map, exactly as the
  // deferred drain would ([temp.inst]/5: the specialization's definition
  // is instantiated because its existence affects the semantics -- here,
  // a constant expression needs its value).  Failure restores the no-body
  // state; the enclosing evaluation treats it as non-constant.
  cpp_saved_template_mapt saved_map(template_map);
  template_map = entry->template_map;
  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  try
  {
    convert_function(*method_symbol);
  }
  catch(...)
  {
    method_symbol->value.make_nil();
  }
  get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
  return method_symbol->value.is_not_nil();
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
          // N5008 [temp.spec.partial.match]: for an instance of a PARTIAL
          // specialization the parameters were bound by deduction against
          // the argument pattern; the positional build above cannot
          // reconstruct pack bindings (`pf<Op, index_sequence<Idx...>>`'s
          // non-type `Idx`).  Replay the deduction-time bindings persisted
          // on the class symbol (#spec_template_packs), non-overriding --
          // mirroring resolve()'s scope-walk replay.
          const irept &bindings =
            class_sym->type.find(irep_idt{"#spec_template_packs"});
          for(const auto &entry : bindings.get_sub())
          {
            const irep_idt pid = entry.get(ID_identifier);
            if(pid.empty())
              continue;
            if(entry.id() == irep_idt{"pack_types"})
            {
              if(
                method_map.pack_size_map.find(pid) !=
                method_map.pack_size_map.end())
                continue;
              std::vector<typet> elems;
              for(const auto &t : entry.get_sub())
                elems.push_back(static_cast<const typet &>(t));
              method_map.pack_size_map[pid] = elems.size();
              if(!elems.empty())
              {
                if(elems.size() == 1)
                  method_map.type_map.emplace(pid, elems.front());
                method_map.pack_args_map[pid] = std::move(elems);
              }
            }
            else if(entry.id() == irep_idt{"pack_exprs"})
            {
              if(
                method_map.pack_size_map.find(pid) !=
                method_map.pack_size_map.end())
                continue;
              std::vector<exprt> vals;
              for(const auto &v : entry.get_sub())
                vals.push_back(static_cast<const exprt &>(v));
              method_map.pack_size_map[pid] = vals.size();
              if(!vals.empty())
              {
                if(vals.size() == 1)
                  method_map.expr_map.emplace(pid, vals.front());
                method_map.pack_expr_map[pid] = std::move(vals);
              }
            }
            else if(entry.id() == irep_idt{"scalar_type"})
            {
              if(
                !entry.get_sub().empty() &&
                method_map.type_map.find(pid) == method_map.type_map.end())
              {
                method_map.type_map.emplace(
                  pid, static_cast<const typet &>(entry.get_sub().front()));
              }
            }
            else if(entry.id() == irep_idt{"scalar_expr"})
            {
              if(
                !entry.get_sub().empty() &&
                method_map.expr_map.find(pid) == method_map.expr_map.end())
              {
                method_map.expr_map.emplace(
                  pid, static_cast<const exprt &>(entry.get_sub().front()));
              }
            }
          }
        }
      }
    }
    bool defer = false;
    bool auto_member_of_instance = false;
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
          // ... except members with an undeduced auto return type: per
          // N5008 [dcl.spec.auto.general]/13 the deduced return type is
          // obtained from the definition, and any use of the member in a
          // context that needs its type requires that deduction to have
          // happened.  A deferred instance would keep the placeholder in
          // its symbol type, so a later call site typechecks against
          // `auto` and mis-converts (the non-member/declarator path
          // already converts such functions eagerly for the same
          // reason).  Members of NON-template classes keep the normal
          // queue: their auto returns are deduced on demand at the call
          // site, and an eager conversion here would run while the
          // class is still being elaborated.
          if(has_auto(_method_symbol->type))
          {
            defer = false;
            auto_member_of_instance = true;
          }
        }
      }
    }

    if(defer)
    {
      deferred_method_bodies.emplace(
        _method_symbol->name,
        method_bodyt(_method_symbol, method_map, instantiation_stack));
    }
    else if(auto_member_of_instance && _method_symbol->value.is_not_nil())
    {
      // Undeduced auto return type: per N5008 [dcl.spec.auto.general]/13
      // the deduced type comes from the definition, and the call site
      // being typechecked right now needs it -- convert eagerly under
      // the method's template map instead of queueing (the queue drains
      // only after the whole translation unit, far too late for the
      // pending conversion at the call).  Mirrors the eager conversion
      // in cpp_declarator_convertert for non-member auto functions.
      template_mapt old_map;
      old_map.swap(template_map);
      template_map = method_map;
      try
      {
        convert_function(*_method_symbol);
        deferred_typechecking.erase(_method_symbol->name);
      }
      catch(...)
      {
        _method_symbol->value.make_nil();
      }
      template_map.swap(old_map);
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

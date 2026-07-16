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

#include <functional>
#include <ostream>
#include <set>
#include <string>

const std::vector<typet> *
template_mapt::function_parameter_pack(const typet &param_type) const
{
  // A function parameter pack appears as a parameter whose type is a bare
  // reference to a template parameter pack, e.g. `_ArgTypes` in
  // `_Res(_ArgTypes...)`.  Match it by (suffix of) identifier against the
  // deduced packs.  A bare cpp_name with a single `name` component is
  // required so that qualified names or template-ids are not
  // misinterpreted as packs.
  if(param_type.id() != ID_cpp_name)
    return nullptr;
  const irept::subt &sub = param_type.get_sub();
  if(sub.size() != 1 || sub.front().id() != ID_name)
    return nullptr;
  const std::string base = id2string(sub.front().get(ID_identifier));
  for(const auto &entry : pack_args_map)
  {
    const std::string key = id2string(entry.first);
    const auto p = key.rfind("::");
    if((p != std::string::npos ? key.substr(p + 2) : key) == base)
      return &entry.second;
  }
  // A pack deduced to zero elements has no pack_args_map entry, only a
  // pack_size_map entry of value 0; expand it to an empty parameter list.
  static const std::vector<typet> empty_pack;
  for(const auto &entry : pack_size_map)
  {
    if(entry.second != 0)
      continue;
    const std::string key = id2string(entry.first);
    const auto p = key.rfind("::");
    if((p != std::string::npos ? key.substr(p + 2) : key) == base)
      return &empty_pack;
  }
  return nullptr;
}

void template_mapt::expand_parameter_packs(typet &function_type) const
{
  if(function_type.id() != ID_code && function_type.id() != ID_function_type)
    return;

  irept::subt &parameters = function_type.add(ID_parameters).get_sub();
  irept::subt new_parameters;
  for(auto &parameter : parameters)
  {
    if(parameter.id() == ID_parameter || parameter.id() == ID_cpp_declaration)
    {
      const std::vector<typet> *pack = function_parameter_pack(
        static_cast<const typet &>(parameter.find(ID_type)));
      if(pack != nullptr)
      {
        // [temp.variadic]/5: replace the pack-expansion parameter with
        // one parameter per deduced pack element.
        //
        // When more than one element is produced, give each replicated
        // parameter a distinct name `base$k` (mirroring the in-class
        // `compound_type` expansion), so that the function-body uses of the
        // pack -- e.g. `fp(a...)`, the libstdc++
        // `function<R(A...)>::operator()` body
        // `_M_invoker(_M_functor, std::forward<A>(__args)...)` -- can be
        // expanded to the matching `base$0..base$k-1` arguments.  Without
        // distinct names the N replicated parameters collide under one name and
        // the body call collapses to a single argument.  A single-element pack
        // keeps the original name (handled by the single-element substitution
        // in cpp_typecheck_method_bodies).
        irep_idt pack_base_name;
        if(pack->size() >= 2)
        {
          for(const auto &d : parameter.get_sub())
            if(d.id() == ID_cpp_declarator)
            {
              for(const auto &nn : d.find(ID_name).get_sub())
                if(nn.id() == ID_name && !nn.get(ID_identifier).empty())
                {
                  pack_base_name = nn.get(ID_identifier);
                  break;
                }
              break;
            }
        }
        std::size_t pack_index = 0;
        for(const auto &pt : *pack)
        {
          irept expanded = parameter;
          static_cast<typet &>(expanded.add(ID_type)) = pt;
          // [dcl.ref] reference collapsing: a forwarding-reference pack
          // `A&&...` expands each element E to the reference formed by
          // applying the declarator's reference to E.  When the deduced
          // element type already carries a reference part -- as the
          // forwarding-reference deduction in guess_function_template_args
          // records it -- use that and drop the declarator reference to avoid
          // doubling.  Otherwise (e.g. a class template partial specialization
          // whose pack is bound to bare element types) keep the declarator's
          // reference so the expanded parameter is `E&`/`E&&` and not a
          // by-value `E` -- losing it makes e.g.
          // `_Function_handler::_M_invoke(_Any_data&, _ArgTypes&&...)`'s type
          // mismatch the function's `_M_invoker` pointer.
          const bool element_is_reference =
            (pt.id() == ID_frontend_pointer || pt.id() == ID_pointer) &&
            (pt.get_bool(ID_C_reference) || pt.get_bool(ID_C_rvalue_reference));
          for(auto &d : expanded.get_sub())
            if(d.id() == ID_cpp_declarator)
            {
              const typet &dtype = static_cast<const typet &>(d.find(ID_type));
              const bool declarator_is_reference =
                (dtype.id() == ID_frontend_pointer ||
                 dtype.id() == ID_pointer) &&
                (dtype.get_bool(ID_C_reference) ||
                 dtype.get_bool(ID_C_rvalue_reference));
              if(element_is_reference || !declarator_is_reference)
                static_cast<typet &>(d.add(ID_type)).make_nil();
              d.remove(ID_ellipsis);
              if(!pack_base_name.empty())
              {
                const std::string nm =
                  id2string(pack_base_name) + "$" + std::to_string(pack_index);
                for(auto &nn : d.add(ID_name).get_sub())
                  if(nn.id() == ID_name)
                  {
                    nn.set(ID_identifier, nm);
                    break;
                  }
              }
            }
          new_parameters.push_back(expanded);
          ++pack_index;
        }
        continue;
      }
    }
    new_parameters.push_back(parameter);
  }
  parameters.swap(new_parameters);
}

/// Substitute, in place, every reference to the type parameter pack named
/// \p base (matched by short-name suffix) appearing inside \p n with the
/// concrete element type \p elem ([temp.variadic]/5): in the k-th expanded
/// copy of a pack expansion the pack reference becomes the k-th deduced
/// element type.  The pack reference is replaced both when it is a node's
/// `ID_type` (a type template argument) and when it is a bare `cpp_name`
/// sub-node -- the latter so a pack nested inside a reference type, e.g. the
/// `Args` in `static_cast<Args&&>(a)` (the forwarding cast of libstdc++'s
/// variadic `std::__invoke`), is substituted (yielding `elem&&`, performing
/// [dcl.ref] reference collapsing).
static void
replace_type_pack_ref(irept &n, const std::string &base, const typet &elem)
{
  const auto is_pack_ref = [&base](const irept &t) -> bool
  {
    if(
      t.id() != ID_cpp_name || t.get_sub().size() != 1 ||
      t.get_sub().front().id() != ID_name)
      return false;
    const std::string nm = id2string(t.get_sub().front().get(ID_identifier));
    const auto p = nm.rfind("::");
    return (p != std::string::npos ? nm.substr(p + 2) : nm) == base;
  };

  if(is_pack_ref(n.find(ID_type)))
    static_cast<irept &>(n.add(ID_type)) = elem;
  for(auto &s : n.get_sub())
  {
    if(is_pack_ref(s))
      s = elem;
    else
      replace_type_pack_ref(s, base, elem);
  }
  for(auto &ns : n.get_named_sub())
  {
    if(is_pack_ref(ns.second))
      ns.second = elem;
    else
      replace_type_pack_ref(ns.second, base, elem);
  }
}

void template_mapt::expand_call_argument_packs(irept &n, bool only_nontype)
  const
{
  // N5008 [temp.inst]/2: instantiating a class template does not instantiate
  // its member TEMPLATES -- their bodies still reference their OWN parameter
  // packs, to be expanded only when the member template itself is
  // instantiated.  Recursing into a nested template declaration here would
  // expand (and CONSUME, stripping the `...`) a pack expansion such as
  // `_Up(std::forward<_Args>(__args)...)` in __new_allocator::construct's
  // body against the ENCLOSING class instantiation's unrelated pack sizes,
  // leaving the member template's body unexpandable at its later
  // instantiation.  Skip nested template declarations.
  if(n.id() == ID_cpp_declaration && n.get_bool(ID_is_template))
    return;

  for(auto &s : n.get_sub())
    expand_call_argument_packs(s, only_nontype);
  for(auto &ns : n.get_named_sub())
    expand_call_argument_packs(ns.second, only_nontype);

  const bool is_new =
    n.id() == ID_side_effect && n.get(ID_statement) == ID_cpp_new;
  if(!(n.id() == ID_side_effect &&
       (n.get(ID_statement) == ID_function_call || is_new)))
    return;

  // N5008 [temp.variadic]/5 + [expr.new]: a new-initializer's
  // expression-list is a pack-expansion context exactly like a
  // function-call argument list -- e.g. std::construct_at's trailing return
  // type `decltype(::new((void*)0) _Tp(declval<_Args>()...))`.  Expand its
  // elements with the same per-argument logic; for a function call, expand
  // the ID_arguments operand.
  irept *child_ptr = nullptr;
  if(is_new)
    child_ptr = &n.add(ID_initializer);
  else
    for(auto &c : n.get_sub())
      if(c.id() == ID_arguments)
      {
        child_ptr = &c;
        break;
      }
  if(child_ptr != nullptr)
  {
    irept &child = *child_ptr;

    bool changed = false;
    irept::subt new_args;
    for(auto &arg : child.get_sub())
    {
      if(!arg.get_bool(ID_ellipsis))
      {
        new_args.push_back(arg);
        continue;
      }

      // Locate the type parameter pack referenced inside this argument: a
      // type template argument that is a bare cpp_name whose short name
      // matches a deduced pack.
      const std::vector<typet> *elems = nullptr;
      // Or a NON-type parameter pack whose element VALUES are recorded in
      // pack_expr_map (e.g. the `I` in `add(I...)`, a non-type template
      // parameter pack expanded as call arguments -- N5008 [temp.variadic]/5).
      const std::vector<exprt> *val_elems = nullptr;
      std::string base;
      bool empty_pack = false;
      // Match a candidate node \p t that is a bare cpp_name (single name
      // component) against the deduced packs by short name.  Records the
      // element list (non-empty pack) or the empty-pack flag and returns
      // whether it matched.
      auto match_pack = [&](const irept &t) -> bool
      {
        if(
          t.id() != ID_cpp_name || t.get_sub().size() != 1 ||
          t.get_sub().front().id() != ID_name)
          return false;
        const std::string nm =
          id2string(t.get_sub().front().get(ID_identifier));
        const auto p = nm.rfind("::");
        const std::string suf = p != std::string::npos ? nm.substr(p + 2) : nm;
        for(const auto &pe : pack_args_map)
        {
          const std::string key = id2string(pe.first);
          const auto q = key.rfind("::");
          const std::string ksuf =
            q != std::string::npos ? key.substr(q + 2) : key;
          if(ksuf == suf)
          {
            elems = &pe.second;
            base = suf;
            return true;
          }
        }
        for(const auto &pe : pack_expr_map)
        {
          const std::string key = id2string(pe.first);
          const auto q = key.rfind("::");
          const std::string ksuf =
            q != std::string::npos ? key.substr(q + 2) : key;
          if(ksuf == suf)
          {
            val_elems = &pe.second;
            base = suf;
            return true;
          }
        }
        for(const auto &ps : pack_size_map)
        {
          if(ps.second != 0)
            continue;
          const std::string key = id2string(ps.first);
          const auto q = key.rfind("::");
          const std::string ksuf =
            q != std::string::npos ? key.substr(q + 2) : key;
          if(ksuf == suf)
          {
            empty_pack = true;
            base = suf;
            return true;
          }
        }
        return false;
      };
      std::function<void(const irept &)> find = [&](const irept &m)
      {
        if(elems != nullptr || val_elems != nullptr || empty_pack)
          return;
        // The pack may be the argument's own type (e.g. `declval<A>()`, whose
        // `A` is the node's ID_type) or a bare cpp_name nested anywhere in the
        // argument -- e.g. the `Args` inside the reference type of
        // `static_cast<Args&&>(a)` (libstdc++'s variadic `std::__invoke`
        // forwarding cast), which is not surfaced by ID_type because it sits
        // inside the reference.  Check both.  [temp.variadic]/5,6.
        if(match_pack(m.find(ID_type)) || match_pack(m))
          return;
        for(const auto &s : m.get_sub())
          find(s);
        for(const auto &nss : m.get_named_sub())
          find(nss.second);
      };
      find(arg);

      // N5008 [temp.variadic]/5: a NON-type parameter pack expanded as call
      // arguments (`add(I...)`) -- expand to one argument per element,
      // substituting the pack's k-th VALUE for its bare cpp_name reference.
      if(val_elems != nullptr)
      {
        changed = true;
        for(const exprt &ve : *val_elems)
        {
          irept copy = arg;
          copy.remove(ID_ellipsis);
          std::function<void(irept &)> repl = [&](irept &m)
          {
            if(
              m.id() == ID_cpp_name && m.get_sub().size() == 1 &&
              m.get_sub().front().id() == ID_name)
            {
              const std::string nm =
                id2string(m.get_sub().front().get(ID_identifier));
              const auto p = nm.rfind("::");
              if((p != std::string::npos ? nm.substr(p + 2) : nm) == base)
              {
                m = ve;
                return;
              }
            }
            for(auto &s : m.get_sub())
              repl(s);
            for(auto &ns : m.get_named_sub())
              repl(ns.second);
          };
          repl(copy);
          new_args.push_back(copy);
        }
        continue;
      }

      if(empty_pack)
      {
        if(only_nontype)
        {
          new_args.push_back(arg);
          continue;
        }
        changed = true;
        continue; // zero-length expansion: drop the argument
      }

      if(elems == nullptr)
      {
        if(only_nontype)
        {
          // In only-nontype mode leave a value / function-parameter pack
          // expansion untouched: it is driven by pack_size_map, which in a
          // nested eager convert_function may belong to an unrelated enclosing
          // instantiation, and this body's function-parameter pack was already
          // expanded at instantiation time.
          new_args.push_back(arg);
          continue;
        }
        // N5008 [temp.variadic]/4,5: the argument carries `...` (so it is a
        // pack expansion) but its pattern references no *type* parameter pack
        // -- it is a *value* parameter pack expansion, e.g. `f(a...)` whose
        // `a` is a function parameter pack (the shape of a by-value variadic
        // forwarding helper's trailing-return `decltype(f(a...))`).  There is
        // no type to substitute; the expansion is N copies of the pattern,
        // each referencing the single in-scope value parameter (whose deduced
        // element type fixes the call-argument's type), where N is the common
        // length of the packs in the expansion ([temp.variadic]/5).  Use the
        // unique non-zero deduced pack size; if every deduced pack is empty the
        // expansion is empty (drop the argument); if the size is ambiguous
        // (several distinct non-zero sizes) leave the argument untouched.
        std::set<std::size_t> sizes;
        bool any_pack = false;
        for(const auto &ps : pack_size_map)
        {
          any_pack = true;
          if(ps.second != 0)
            sizes.insert(ps.second);
        }
        if(any_pack && sizes.empty())
        {
          changed = true;
          continue; // zero-length value-pack expansion: drop the argument
        }
        if(sizes.size() == 1)
        {
          changed = true;
          const std::size_t n = *sizes.begin();
          for(std::size_t i = 0; i < n; ++i)
          {
            irept copy = arg;
            copy.remove(ID_ellipsis);
            new_args.push_back(copy);
          }
          continue;
        }
        // Size unknown or ambiguous: leave untouched so existing handling is
        // unaffected.
        new_args.push_back(arg);
        continue;
      }

      changed = true;
      for(const typet &elem : *elems)
      {
        irept copy = arg;
        copy.remove(ID_ellipsis);
        replace_type_pack_ref(copy, base, elem);
        new_args.push_back(copy);
      }
    }
    if(changed)
      child.get_sub() = new_args;
  }
}

void template_mapt::apply(typet &type) const
{
  // N5008 [temp.variadic]/5: a `decltype` operand may contain a function-call
  // argument pack expansion (e.g. `decltype(declval<F>()(declval<A>()...))`,
  // the shape of libstdc++'s `__invoke_result`).  Expand it here -- before the
  // substitution recursion below -- so the operand becomes a concrete call
  // (`...(declval<E0>(), declval<E1>())`) that elaborates; otherwise the bare
  // pack reference is rejected and e.g. multi-argument std::function fails to
  // construct.  Restricted to decltype operands to leave all other contexts
  // untouched.
  if(type.id() == ID_decltype)
    expand_call_argument_packs(type);

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
    if(!to_array_type(type).size().is_nil())
      apply(to_array_type(type).size());
  }
  else if(type.id()==ID_pointer)
  {
    // N5008 [temp.variadic]/5: a pointer-to-function data member whose pointee
    // type contains a pack expansion of the enclosing class parameter pack --
    // e.g. the `_Res(*)(const _Any_data&, _ArgTypes&&...)` invoker pointer in
    // libstdc++'s `function<_Res(_ArgTypes...)>` -- must have that pack
    // expanded into one parameter per deduced element BEFORE the parameters
    // are substituted below; otherwise the substitution replaces the pack with
    // a single (scalar) element and the pointer type is collapsed to one
    // parameter (so e.g. assigning the correctly-arity'd
    // `&_Function_handler<_Res(A...), F>::_M_invoke` to it fails).
    // `expand_parameter_packs` is a no-op unless the pointee is a function type
    // with a parameter that names a pack recorded in `pack_args_map` (the class
    // pack), so method types and non-function pointees are untouched.
    expand_parameter_packs(to_pointer_type(type).base_type());
    apply(to_pointer_type(type).base_type());
  }
  else if(type.id() == ID_frontend_pointer)
  {
    // A pointer/reference written in source is an `ID_frontend_pointer`
    // (turned into `ID_pointer` only during type-checking) whose pointee is
    // its `subtype`.  Recurse into it so that template parameters appearing
    // in a pointer/reference pattern -- e.g. the `Ts` in a pack expansion
    // `Ts&...` or `const Ts&...`, the shape of std::tuple's
    // `const _Elements&...` constructor arguments -- are substituted.
    // As in the ID_pointer branch above, first expand an enclosing-class
    // parameter pack in a (pre-conversion) function-pointer pointee's
    // parameter list ([temp.variadic]/5), so a function-pointer data member is
    // not collapsed to a single parameter.
    expand_parameter_packs(to_type_with_subtype(type).subtype());
    apply(to_type_with_subtype(type).subtype());
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
      {
        apply(static_cast<typet &>(base.add(ID_type)));
        // Base class specifiers store the class name in ID_name
        // (as a cpp_name).  Expand pack parameters in the base
        // class template arguments.  We only touch the
        // template_args sub-nodes to avoid disturbing other
        // name components.
        if(!pack_args_map.empty() && base.find(ID_name).id() == ID_cpp_name)
        {
          for(auto &s : base.add(ID_name).get_sub())
          {
            if(s.id() == ID_template_args)
            {
              irept::subt &args = s.add(ID_arguments).get_sub();
              // Expand pack parameters
              irept::subt expanded;
              for(auto &arg : args)
              {
                bool was_pack = false;
                if(arg.id() == ID_type)
                {
                  const typet &at = static_cast<const exprt &>(arg).type();
                  if(at.id() == ID_template_parameter_symbol_type)
                  {
                    const irep_idt &pid =
                      to_template_parameter_symbol_type(at).get_identifier();
                    for(const auto &pe : pack_args_map)
                    {
                      if(pe.first == pid)
                      {
                        for(const auto &pt : pe.second)
                          expanded.push_back(
                            static_cast<const irept &>(type_exprt{pt}));
                        was_pack = true;
                        break;
                      }
                    }
                  }
                }
                if(!was_pack)
                {
                  apply(static_cast<exprt &>(arg));
                  if(!(arg.id() == ID_type &&
                       static_cast<const exprt &>(arg).type().id() == ID_empty))
                    expanded.push_back(arg);
                }
              }
              args = expanded;
            }
          }
        }
      }
    }

    // Traverse the body sub-tree (member declarations).
    // This handles template template parameter substitution in
    // using declarations within template bodies.
    if(type.find(ID_body).is_not_nil())
    {
      for(auto &op : type.add(ID_body).get_sub())
      {
        irept &decl_type = op.add(ID_type);

        // [temp.local]/1 + [basic.scope.temp]: a member template's own
        // parameters shadow same-named parameters of an enclosing
        // template.  A member alias template's body stores parameter
        // references as bare `cpp_name`s; for the canonical
        // `template<class _Tp, ...> using type = _Tp;` form (libstdc++
        // `__conditional`), `apply`'s short-name matching would bind the
        // top-level body reference to an unrelated enclosing parameter
        // of the same name that happens to be in scope (e.g.
        // `std::decay<_Tp>`'s `_Tp` leaking into
        // `std::__conditional<C>::type<_Tp,_>`), baking in the wrong
        // type before the member alias is itself instantiated.
        //
        // Protect ONLY top-level bare references (direct children of the
        // body), not references nested inside `decltype`/template
        // arguments -- those are handled by existing machinery that
        // other library code relies on.  Append a sentinel so the
        // short-name match misses, substitute, then strip it so the
        // member alias's own instantiation binds the reference by its
        // own parameter identity ([temp.res] two-phase).
        const bool is_member_alias = (op.get_bool(ID_is_template) ||
                                      op.find(ID_template_type).is_not_nil()) &&
                                     op.get_bool(ID_is_typedef);
        std::set<std::string> own_param_names;
        if(is_member_alias)
        {
          const auto short_name = [](const irep_idt &id) -> std::string
          {
            const std::string s = id2string(id);
            const auto p = s.rfind("::");
            return p != std::string::npos ? s.substr(p + 2) : s;
          };
          for(const auto &param :
              op.find(ID_template_type).find(ID_template_parameters).get_sub())
          {
            for(const auto &d : param.get_sub())
            {
              if(d.id() != ID_cpp_declarator)
                continue;
              for(const auto &ns : d.find(ID_name).get_sub())
                if(ns.id() == ID_name && !ns.get(ID_identifier).empty())
                  own_param_names.insert(short_name(ns.get(ID_identifier)));
            }
          }
        }
        if(is_member_alias && !own_param_names.empty())
        {
          const std::string marker = "#tmpl_param_shadow";
          const auto mark = [&](irept &n, bool restore)
          {
            if(
              n.id() != ID_cpp_name || n.get_sub().size() != 1 ||
              n.get_sub().front().id() != ID_name)
              return;
            irept &nm = n.get_sub().front();
            const std::string s = id2string(nm.get(ID_identifier));
            if(!restore)
            {
              const auto p = s.rfind("::");
              const std::string nn =
                p != std::string::npos ? s.substr(p + 2) : s;
              if(own_param_names.count(nn) != 0)
                nm.set(ID_identifier, s + marker);
            }
            else if(
              s.size() >= marker.size() &&
              s.compare(s.size() - marker.size(), marker.size(), marker) == 0)
              nm.set(ID_identifier, s.substr(0, s.size() - marker.size()));
          };
          const auto each = [&](bool restore)
          {
            for(auto &sub : decl_type.get_sub())
            {
              mark(sub, restore);
              if(sub.id() == ID_merged_type)
                for(auto &ss : sub.get_sub())
                  mark(ss, restore);
            }
          };
          each(false);
          // N5008 [temp.alias]/2 + [temp.variadic]/4-5: while substituting this
          // member alias template's body during the enclosing class's
          // instantiation, its OWN parameters are not yet bound.  Record their
          // short names so the nested-pack expander defers any pack expansion
          // whose pattern references one (rather than expanding it over the
          // enclosing class pack alone and leaving the alias's own pack
          // dangling).  Saved/restored to nest correctly.
          std::set<std::string> saved_deferred =
            std::move(deferred_own_pack_names);
          deferred_own_pack_names = own_param_names;
          for(auto &sub : decl_type.get_sub())
            apply(static_cast<typet &>(sub));
          deferred_own_pack_names = std::move(saved_deferred);
          each(true);
        }
        else
        {
          for(auto &sub : decl_type.get_sub())
            apply(static_cast<typet &>(sub));
        }

        // [temp.variadic]/5: expand a function parameter pack that names
        // the enclosing class template's parameter pack in a member
        // function declarator (e.g. `R operator()(A...)` of
        // `std::function<R(A...)>`), whose function type is carried by
        // the declarator rather than the declaration's type.
        //
        // Scope: only members whose declaration type is a return type
        // (skip constructors/destructors, which have their own
        // empty-pack handling in cpp_instantiate_template), and only
        // packs recorded in pack_args_map/pack_size_map (the enclosing
        // class pack) -- a member function template's own parameter
        // pack is not recorded there and so is left untouched, to be
        // deduced per call.
        if(decl_type.id() == ID_constructor || decl_type.id() == ID_destructor)
          continue;
        // A member function template has its own parameter pack, which
        // must be deduced per call rather than expanded with the
        // enclosing class pack ([temp.variadic], [temp.deduct.call]);
        // leave it untouched.
        if(
          op.get_bool(ID_is_template) || op.find(ID_template_type).is_not_nil())
          continue;
        for(auto &d : op.get_sub())
        {
          if(d.id() != ID_cpp_declarator)
            continue;
          typet &dt = static_cast<typet &>(d.add(ID_type));
          if(dt.id() != ID_function_type && dt.id() != ID_code)
            continue;
          bool has_class_pack = false;
          for(const auto &p : dt.find(ID_parameters).get_sub())
          {
            if(p.id() != ID_cpp_declaration && p.id() != ID_parameter)
              continue;
            if(
              function_parameter_pack(
                static_cast<const typet &>(p.find(ID_type))) != nullptr)
              has_class_pack = true;
          }
          if(has_class_pack)
            expand_parameter_packs(dt);
        }
      }
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
      //
      // CONFORMANCE WARNING (Violation V1, see doc/architectural/
      // cpp-frontend-review-2026-06-24-template-map-scope.md): this resolves a
      // bare parameter reference by SHORT NAME (suffix after the last "::")
      // across the whole flat map, violating N5008 [basic.scope.temp]/2
      // (parameter identity is scope + name).  When an unrelated live
      // instantiation has a same-named parameter, this can substitute the wrong
      // binding -- the root of the recurring cross-template "pack bleed".  The
      // `#tmpl_param_shadow` marker below and the shadow-removal loop in
      // build() are patches around this; the structural fix is to resolve only
      // by exact scope-qualified identifier.
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
            // For template template parameters: when the mapped type
            // is a template_parameter_symbol_type and the cpp_name has
            // template_args, replace only the name (preserving args).
            // Per C++ standard, template template parameter substitution
            // replaces the template name, not the template arguments.
            if(
              has_targs &&
              entry.second.id() == ID_template_parameter_symbol_type)
            {
              const irep_idt &tmpl_id =
                to_template_parameter_symbol_type(entry.second)
                  .get_identifier();
              // Extract base name from the template identifier
              std::string tmpl_str = id2string(tmpl_id);
              auto last_sep = tmpl_str.rfind("::");
              std::string tmpl_base = last_sep != std::string::npos
                                        ? tmpl_str.substr(last_sep + 2)
                                        : tmpl_str;
              // Remove template suffix if present
              auto angle = tmpl_base.find('<');
              if(angle != std::string::npos)
                tmpl_base = tmpl_base.substr(0, angle);
              // Strip 'template.' prefix if present
              if(tmpl_base.substr(0, 9) == "template.")
                tmpl_base = tmpl_base.substr(9);
              // Build a qualified name from the full identifier.
              // E.g., Tester::template._Apply<Type0> becomes
              // Tester::_Apply with template_args preserved.
              if(last_sep != std::string::npos)
              {
                std::string prefix = tmpl_str.substr(0, last_sep);
                irept::subt new_subs;
                std::size_t pos2 = 0;
                while(pos2 < prefix.size())
                {
                  auto next = prefix.find("::", pos2);
                  std::string part;
                  if(next == std::string::npos)
                  {
                    part = prefix.substr(pos2);
                    pos2 = prefix.size();
                  }
                  else
                  {
                    part = prefix.substr(pos2, next - pos2);
                    pos2 = next + 2;
                  }
                  if(!part.empty())
                  {
                    irept name_sub{ID_name};
                    name_sub.set(ID_identifier, part);
                    new_subs.push_back(std::move(name_sub));
                    new_subs.push_back(irept{"::"});
                  }
                }
                irept base_sub{ID_name};
                base_sub.set(ID_identifier, tmpl_base);
                new_subs.push_back(std::move(base_sub));
                for(std::size_t si = 1; si < sub.size(); si++)
                  new_subs.push_back(sub[si]);
                sub = std::move(new_subs);
              }
              else
              {
                sub.front() = irept{ID_name};
                sub.front().set(ID_identifier, tmpl_base);
              }
              return;
            }
            // Template-template-parameter substitution where the
            // binding is a class-template instance (struct_tag), e.g.
            // `_SomeTemplate -> tag-allocator<tag-A>` from binding a
            // TT-param to the WHOLE instance during deduction.  The
            // cpp_name `_SomeTemplate<_Up, _Types...>` should yield
            // `allocator<_Up, _Types...>` so the args-substitution
            // loop below can substitute `_Up` and expand the pack.
            // Without this, `type = entry.second` replaces the entire
            // expression with `tag-allocator<tag-A>` and ignores the
            // cpp_name's template_args.
            //
            // Only apply this rewrite when the cpp_name is purely the
            // TT-param + its immediate template_args (no `::` in
            // `sub` apart from the optional leading scope chain that
            // resolves to the SAME entry).  When the cpp_name is a
            // QUALIFIED form like `_Tp::rebind<_Up>::other`, the
            // `_Tp` token is acting as a scope qualifier rather than
            // as a TT-template-name; in that case the existing
            // qualified-name fall-through (below, in the
            // `if(sub.size() > 1 && entry.second.id() == ID_struct_tag)`
            // branch) replaces `_Tp` with the full struct_tag
            // identifier so the subsequent `::rebind<...>` lookup
            // happens in the bound instance's scope.
            bool has_scope_separator = false;
            for(const auto &s : sub)
            {
              if(s.id() == "::")
              {
                has_scope_separator = true;
                break;
              }
            }
            if(
              has_targs && !has_scope_separator &&
              entry.second.id() == ID_struct_tag)
            {
              const std::string ident =
                id2string(to_struct_tag_type(entry.second).get_identifier());
              // Format: "<scope>tag-<base><args>" where <scope> is
              // any (possibly empty) sequence of "name::"-style
              // qualifiers and <args> is the bracketed template args
              // (possibly empty).  `tag-` appears BEFORE base and
              // again, possibly multiple times, INSIDE <args> (for
              // nested instances).  Find the outermost `tag-` at
              // depth 0 and the depth-0 `<` (if any) after it.
              std::size_t tag_pos = std::string::npos;
              std::size_t end_pos = ident.size();
              int depth = 0;
              for(std::size_t i = 0; i < ident.size();)
              {
                if(ident[i] == '<')
                {
                  if(depth == 0 && tag_pos != std::string::npos)
                  {
                    end_pos = i;
                    break;
                  }
                  depth++;
                  i++;
                }
                else if(ident[i] == '>')
                {
                  if(depth > 0)
                    depth--;
                  i++;
                }
                else if(
                  depth == 0 && tag_pos == std::string::npos &&
                  i + 4 <= ident.size() && ident.compare(i, 4, "tag-") == 0)
                {
                  tag_pos = i + 4;
                  i += 4;
                }
                else
                {
                  i++;
                }
              }
              if(tag_pos != std::string::npos && end_pos > tag_pos)
              {
                std::string base_name =
                  ident.substr(tag_pos, end_pos - tag_pos);
                if(!base_name.empty())
                {
                  // Rewrite ONLY the front name; preserve any leading
                  // sub entries (scope qualifiers like `ns::`) and the
                  // trailing template_args entries.  The
                  // args-substitution loop later in `apply` will then
                  // substitute references like `_Up`/`_Types...`
                  // against the current template_map.
                  //
                  // For simple cpp_names with no scope chain in the
                  // sub (sub = [name(_SomeTemplate), template_args]),
                  // the result is sub = [name(<base>), template_args].
                  sub.front() = irept{ID_name};
                  sub.front().set(ID_identifier, base_name);
                  break; // exit for(entry : type_map); fall through
                         // to the args-substitution loop below.
                }
              }
              // Fallback: identifier didn't have the expected
              // `tag-<base>` form (shouldn't happen for instances
              // produced by `class_template_symbol`); preserve the
              // pre-existing behaviour by replacing the whole
              // expression.
              type = entry.second;
              return;
            }
            // Qualified-name case where the TT-param-bound `_Tp`
            // appears as a scope and there ARE template_args
            // somewhere in the sub-tree (e.g.
            // `_Tp::template rebind<_Up>::other`).  The existing
            // qualified-name handler below skips itself when
            // `has_targs` is true, so handle it here: replace the
            // leading `_Tp` name with the bound struct_tag's full
            // identifier and let the args-substitution loop apply
            // the rest.  Without this, the fall-through replaces the
            // whole expression with the bound struct_tag, losing the
            // `::rebind<...>::other` suffix.
            if(has_scope_separator && entry.second.id() == ID_struct_tag)
            {
              irep_idt tag = to_struct_tag_type(entry.second).get_identifier();
              sub.front() = irept{ID_name};
              sub.front().set(ID_identifier, tag);
              break; // exit type_map loop; fall through to the
                     // args-substitution loop so any inner
                     // `<_Up, _Types...>` references get
                     // substituted.
            }
            type = entry.second;
            return;
          }
          // Qualified name like _Up::X where _Up maps to a struct:
          // replace _Up with the struct_tag identifier so scope
          // resolution can find the member via id_map or symbol table.
          if(sub.size() > 1 && entry.second.id() == ID_struct_tag)
          {
            irep_idt tag = to_struct_tag_type(entry.second).get_identifier();
            sub.front() = irept{ID_name};
            sub.front().set(ID_identifier, tag);
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
        // Expand parameter packs in template arguments.
        // Before applying substitutions, check if any arg is a
        // pack parameter and replace it with all pack args.
        irept::subt expanded_args;

        // Helper: an empty-pack reference (a `_Pack...` whose pack
        // resolved to zero elements) has no entry in `pack_args_map`
        // (we only record non-empty packs there) but does have an
        // entry of value `0` in `pack_size_map`.  When walking the
        // arg list, expanding such a reference to "no args" is the
        // correct behaviour; leaving it as the bare cpp_name causes
        // downstream `typecheck_template_args` to fail with
        // "too many template arguments".
        // N5008 [temp.alias]/2 + [temp.inst]/2: a member alias template's OWN
        // parameter pack (deferred_own_pack_names) is not bound during the
        // enclosing instantiation -- it binds only at the alias's point of
        // use.  It must never be collapsed here: the suffix match below is by
        // bare short name, so a stale zero-size entry for a same-named pack
        // of an UNRELATED template (the flat map keeps entries of enclosing
        // and previous builds) would otherwise silently expand it to zero
        // elements (e.g. std::tuple's _ImplicitCtor `_Args...` folding to
        // `__is_implicitly_constructible<>()`, wrongly disabling every
        // constrained tuple constructor at arity >= 3).
        auto matches_empty_pack = [this](irep_idt ident) -> bool
        {
          if(deferred_own_pack_names.count(id2string(ident)) != 0)
            return false;
          for(const auto &ps : pack_size_map)
          {
            if(ps.second != 0)
              continue;
            const std::string &key = id2string(ps.first);
            auto p = key.rfind("::");
            std::string suffix =
              p != std::string::npos ? key.substr(p + 2) : key;
            if(suffix == id2string(ident))
              return true;
          }
          return false;
        };

        for(auto &arg : args)
        {
          bool was_pack = false;
          if(arg.id() == ID_type)
          {
            const typet &arg_type = static_cast<const exprt &>(arg).type();
            if(arg_type.id() == ID_template_parameter_symbol_type)
            {
              const irep_idt &param_id =
                to_template_parameter_symbol_type(arg_type).get_identifier();
              for(const auto &pack_entry : pack_args_map)
              {
                if(pack_entry.first == param_id)
                {
                  // Replace with all pack args
                  for(const auto &pack_type : pack_entry.second)
                  {
                    expanded_args.push_back(
                      static_cast<const irept &>(type_exprt{pack_type}));
                  }
                  was_pack = true;
                  break;
                }
              }
              // Empty pack: drop the bare reference (zero-length
              // expansion).
              if(!was_pack)
              {
                const std::string &key = id2string(param_id);
                auto p = key.rfind("::");
                std::string suffix =
                  p != std::string::npos ? key.substr(p + 2) : key;
                if(matches_empty_pack(suffix))
                  was_pack = true;
              }
            }
          }
          // Per [temp.variadic]/5: a pack expansion `_Cond...` in a
          // template argument list may be represented as an
          // `ambiguous` node whose type is a `cpp_name` with
          // `ellipsis=true`.  Expand by matching the identifier
          // against pack_args_map entries (suffix match).
          if(
            !was_pack && arg.id() == "ambiguous" &&
            static_cast<const exprt &>(arg).type().id() == ID_cpp_name &&
            static_cast<const exprt &>(arg).type().get_bool(ID_ellipsis))
          {
            const typet &cname = static_cast<const exprt &>(arg).type();
            const irept::subt &csub = cname.get_sub();
            if(!csub.empty() && csub.front().id() == ID_name)
            {
              irep_idt ident = csub.front().get(ID_identifier);
              for(const auto &pack_entry : pack_args_map)
              {
                const std::string &key = id2string(pack_entry.first);
                auto p = key.rfind("::");
                std::string suffix =
                  p != std::string::npos ? key.substr(p + 2) : key;
                if(suffix == id2string(ident))
                {
                  for(const auto &pack_type : pack_entry.second)
                  {
                    // Wrap as ambiguous(type=T) to match the format
                    // expected by downstream template arg processing.
                    exprt wrapped{"ambiguous"};
                    wrapped.type() = pack_type;
                    expanded_args.push_back(
                      static_cast<const irept &>(std::move(wrapped)));
                  }
                  was_pack = true;
                  break;
                }
              }
              // Empty pack: drop the bare reference.
              if(!was_pack && matches_empty_pack(ident))
                was_pack = true;
            }
          }
          // Bare NON-type parameter pack `T...`: unlike a type pack, whose
          // ellipsis sits on the cpp_name TYPE, a non-type pack's ellipsis sits
          // on the `ambiguous` ARG node.  Expand to its element VALUES from
          // pack_expr_map (N5008 [temp.variadic]/4-5).  Gated on the single
          // name actually naming a recorded non-type pack, so ordinary
          // arg-level-ellipsis arguments are untouched.
          if(
            !was_pack && arg.id() == "ambiguous" && arg.get_bool(ID_ellipsis) &&
            static_cast<const exprt &>(arg).type().id() == ID_cpp_name)
          {
            const irept::subt &csub =
              static_cast<const exprt &>(arg).type().get_sub();
            if(csub.size() == 1 && csub.front().id() == ID_name)
            {
              irep_idt ident = csub.front().get(ID_identifier);
              for(const auto &pe : pack_expr_map)
              {
                const std::string &key = id2string(pe.first);
                auto p = key.rfind("::");
                const std::string suffix =
                  p != std::string::npos ? key.substr(p + 2) : key;
                if(suffix == id2string(ident))
                {
                  for(const auto &val : pe.second)
                    expanded_args.push_back(static_cast<const irept &>(val));
                  was_pack = true;
                  break;
                }
              }
              if(!was_pack && matches_empty_pack(ident))
                was_pack = true;
            }
          }
          // [temp.variadic]/4-5: a pack expansion whose pattern is not
          // simply the bare pack (e.g. `typename W<E>::type...`, where the
          // pack `E` is nested inside the pattern) must be expanded once
          // per pack element, with that element substituted for the pack
          // reference *inside* the pattern.  The cases above only handle a
          // pattern that is itself the bare pack; without this a pattern
          // like make_tuple's `tuple<typename __decay_and_strip<E>::__type
          // ...>` collapses to a single element.
          if(
            !was_pack && arg.id() == "ambiguous" &&
            static_cast<const exprt &>(arg).type().id() == ID_cpp_name &&
            static_cast<const exprt &>(arg).type().get_bool(ID_ellipsis))
          {
            // Collect the parameter packs referenced anywhere in the
            // pattern (suffix match against the recorded packs).
            std::set<irep_idt> referenced_packs;
            std::function<void(const irept &)> collect = [&](const irept &n)
            {
              const irep_idt id = n.get(ID_identifier);
              if(!id.empty())
              {
                for(const auto &pe : pack_args_map)
                {
                  const std::string &key = id2string(pe.first);
                  auto p = key.rfind("::");
                  const std::string suffix =
                    p != std::string::npos ? key.substr(p + 2) : key;
                  if(suffix == id2string(id))
                    referenced_packs.insert(pe.first);
                }
                for(const auto &pe : pack_expr_map)
                {
                  const std::string &key = id2string(pe.first);
                  auto p = key.rfind("::");
                  const std::string suffix =
                    p != std::string::npos ? key.substr(p + 2) : key;
                  if(suffix == id2string(id))
                    referenced_packs.insert(pe.first);
                }
                // An EMPTY pack (deduced/explicit zero elements) has no
                // pack_args_map / pack_expr_map entry -- only a pack_size_map
                // entry of value 0.  Include it so a non-bare pattern that
                // references it (e.g. `identity<E>::type...` with E = <>) is
                // recognised as a pack expansion and collapses to zero
                // arguments, rather than being left as a bare, unresolved pack
                // reference (N5008 [temp.variadic]/4,7).
                for(const auto &ps : pack_size_map)
                {
                  const std::string &key = id2string(ps.first);
                  auto p = key.rfind("::");
                  const std::string suffix =
                    p != std::string::npos ? key.substr(p + 2) : key;
                  if(suffix == id2string(id))
                    referenced_packs.insert(ps.first);
                }
              }
              for(const auto &c : n.get_named_sub())
                collect(c.second);
              for(const auto &c : n.get_sub())
                collect(c);
            };
            collect(static_cast<const exprt &>(arg).type());

            // [temp.alias]/2 + [temp.variadic]/4-5: if this pack expansion is
            // in a member alias template's body being substituted during the
            // enclosing class's instantiation, and its pattern references the
            // alias's OWN (not yet bound) parameter, leave it UNEXPANDED.
            // Expanding now would be driven by the enclosing class pack alone,
            // leaving the alias's own pack dangling (e.g. `same_t<Us,Types>::v
            // ...` over `Types` only).  It is expanded later, at the alias's
            // point of use, when its own pack is bound.
            bool defer_for_own_pack = false;
            if(!deferred_own_pack_names.empty())
            {
              std::function<void(const irept &)> scan = [&](const irept &n)
              {
                const irep_idt id = n.get(ID_identifier);
                if(!id.empty())
                {
                  const std::string s = id2string(id);
                  const auto p = s.rfind("::");
                  const std::string sn =
                    p != std::string::npos ? s.substr(p + 2) : s;
                  if(deferred_own_pack_names.count(sn) != 0)
                    defer_for_own_pack = true;
                }
                for(const auto &c : n.get_named_sub())
                  scan(c.second);
                for(const auto &c : n.get_sub())
                  scan(c);
              };
              scan(static_cast<const exprt &>(arg).type());
            }

            if(!defer_for_own_pack && !referenced_packs.empty())
            {
              // A referenced pack is either a type pack (pack_args_map) or a
              // non-type pack (pack_expr_map); this helper gives its length.
              auto pack_len = [&](const irep_idt &pid) -> std::size_t
              {
                auto a = pack_args_map.find(pid);
                if(a != pack_args_map.end())
                  return a->second.size();
                auto e = pack_expr_map.find(pid);
                if(e != pack_expr_map.end())
                  return e->second.size();
                return 0;
              };
              // All packs in a single expansion expand in lock-step and
              // therefore must have the same length ([temp.variadic]/5).
              const std::size_t n = pack_len(*referenced_packs.begin());
              bool consistent = true;
              for(const auto &pid : referenced_packs)
                if(pack_len(pid) != n)
                  consistent = false;
              if(consistent)
              {
                for(std::size_t i = 0; i < n; i++)
                {
                  // Bind each referenced pack to its i-th element (as a
                  // scalar) and substitute it inside a copy of the pattern.
                  template_mapt element_map = *this;
                  for(const auto &pid : referenced_packs)
                  {
                    auto a = pack_args_map.find(pid);
                    if(a != pack_args_map.end())
                      element_map.type_map[pid] = a->second[i];
                    else
                    {
                      // Non-type pack: bind the i-th VALUE as a scalar
                      // non-type parameter binding.
                      auto e = pack_expr_map.find(pid);
                      if(e != pack_expr_map.end())
                        element_map.expr_map[pid] = e->second[i];
                    }
                    element_map.pack_args_map.erase(pid);
                    element_map.pack_expr_map.erase(pid);
                    element_map.pack_size_map.erase(pid);
                  }
                  exprt element = static_cast<const exprt &>(arg);
                  element.type().remove(ID_ellipsis);
                  element_map.apply(element.type());
                  expanded_args.push_back(static_cast<const irept &>(element));
                }
                was_pack = true;
              }
            }
          }
          // Generalized pack expansion whose pattern is an EXPRESSION rather
          // than an `ambiguous` cpp_name (e.g. a comma-expression
          // `((void)Pred, true)...`, libc++'s __all/__is_same idiom) is
          // expanded later in typecheck_template_args, which folds the
          // comma-operator per element ([temp.variadic]/4-5, [expr.comma]).
          if(!was_pack)
            expanded_args.push_back(arg);
        }
        args = expanded_args;

        for(auto &arg : args)
          apply(static_cast<exprt &>(arg));
        // Remove empty-type arguments produced by empty parameter
        // packs.  Without this, an empty pack expands to a void
        // argument that poisons downstream template instantiations.
        args.erase(
          std::remove_if(
            args.begin(),
            args.end(),
            [](const irept &arg)
            {
              return arg.id() == ID_type &&
                     static_cast<const exprt &>(arg).type().id() == ID_empty;
            }),
          args.end());
      }
    }

    // Substitute template parameters used as scope qualifiers
    // (e.g., _Next::value where _Next is mapped to a concrete type).
    // Replace the name component with the mapped type's identifier.
    if(sub.size() >= 3 && sub[0].id() == ID_name && sub[1].id() == "::")
    {
      irep_idt scope_base = sub[0].get(ID_identifier);
      for(const auto &entry : type_map)
      {
        const std::string &key = id2string(entry.first);
        auto p = key.rfind("::");
        std::string suffix = p != std::string::npos ? key.substr(p + 2) : key;
        if(
          suffix == id2string(scope_base) &&
          entry.second.id() != ID_unassigned && entry.second.id() != ID_nil)
        {
          if(entry.second.id() == ID_struct_tag)
          {
            sub[0].set(
              ID_identifier, to_struct_tag_type(entry.second).get_identifier());
          }
          break;
        }
      }
    }
  }
}

void template_mapt::apply(exprt &expr) const
{
  // A `sizeof...(Pack)` pack-size query must keep its pack name unsubstituted:
  // it is resolved against pack_size_map later ([expr.sizeof]/5).  In
  // particular, a single-element pack records a convenience type_map[Pack]
  // entry; substituting it here would turn `sizeof...(Pack)` into
  // `sizeof(<element type>)`.
  if(expr.get_bool("#sizeof_pack"))
    return;

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
      expr_map.find(to_symbol_expr(expr).identifier());

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
      irept::subt new_args;
      for(auto &arg : args.get_sub())
      {
        if(arg.id() != ID_ambiguous)
        {
          new_args.push_back(arg);
          continue;
        }
        // The ambiguous node stores the cpp_name in its "type" field
        const irept &inner = arg.find(ID_type);
        if(
          inner.id() != ID_cpp_name || inner.get_sub().size() != 1 ||
          inner.get_sub()[0].id() != ID_name)
        {
          new_args.push_back(arg);
          continue;
        }
        const std::string target =
          id2string(inner.get_sub()[0].get(ID_identifier));

        // N5008 [temp.variadic]/4-5: a bare NON-type parameter pack expansion
        // `T...` in a value-context template-id (e.g. `cnt<T...>::n`) expands
        // to ALL of the pack's element values, not a single scalar.  This is
        // the value-context analogue of the pack expansion in apply(typet).
        if(arg.get_bool(ID_ellipsis))
        {
          bool handled = false;
          for(const auto &pe : pack_expr_map)
          {
            const std::string &key = id2string(pe.first);
            auto p = key.rfind("::");
            const std::string suffix =
              p != std::string::npos ? key.substr(p + 2) : key;
            if(suffix == target)
            {
              for(const auto &val : pe.second)
                new_args.push_back(static_cast<const irept &>(val));
              handled = true;
              break;
            }
          }
          // A non-type pack that resolved to zero elements: drop the bare
          // reference (zero-length expansion).
          if(!handled)
          {
            for(const auto &ps : pack_size_map)
            {
              if(ps.second != 0)
                continue;
              const std::string &key = id2string(ps.first);
              auto p = key.rfind("::");
              const std::string suffix =
                p != std::string::npos ? key.substr(p + 2) : key;
              if(suffix == target)
              {
                handled = true;
                break;
              }
            }
          }
          if(handled)
            continue;
        }

        bool subst = false;
        for(const auto &entry : expr_map)
        {
          const std::string &key = id2string(entry.first);
          if(
            key == target ||
            (key.size() > target.size() + 2 &&
             key.substr(key.size() - target.size()) == target &&
             key[key.size() - target.size() - 1] == ':'))
          {
            new_args.push_back(entry.second);
            subst = true;
            break;
          }
        }
        if(!subst)
          new_args.push_back(arg);
      }
      args.get_sub() = new_args;
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

// Number of matching leading "::"-separated components shared by two
// scope-qualified identifiers.  Used to pick the nearest enclosing scope among
// same-short-name template parameters (N5008 [basic.scope.temp]/2): a reference
// resolves to the parameter of the nearest enclosing template scope, which the
// longest shared leading scope path approximates.  Differing instantiation
// scope-numbers in the trailing component stop the match, so this compares the
// namespace/template path rather than the (often inconsistent) scope-number.
static std::size_t
common_scope_components(const std::string &a, const std::string &b)
{
  std::size_t n = 0, pa = 0, pb = 0;
  while(true)
  {
    const auto na = a.find("::", pa);
    const auto nb = b.find("::", pb);
    const std::string ca =
      a.substr(pa, na == std::string::npos ? std::string::npos : na - pa);
    const std::string cb =
      b.substr(pb, nb == std::string::npos ? std::string::npos : nb - pb);
    if(ca != cb)
      break;
    ++n;
    if(na == std::string::npos || nb == std::string::npos)
      break;
    pa = na + 2;
    pb = nb + 2;
  }
  return n;
}

exprt template_mapt::lookup_by_suffix(
  const std::string &suffix,
  const irep_idt &reference_id) const
{
  const std::string match = "::" + suffix;
  const std::string ref = id2string(reference_id);

  auto is_match = [&](const std::string &key)
  {
    return key.size() >= match.size() &&
           key.compare(key.size() - match.size(), match.size(), match) == 0;
  };

  // Among all live bindings sharing the short name, prefer the one whose
  // scope-qualified identifier shares the longest leading scope path with the
  // reference ([basic.scope.temp]/2 nearest-enclosing-scope).  Type parameters
  // take priority over non-type parameters on a tie (matching the historical
  // type_map-first behaviour), and the first match wins on a further tie
  // (deterministic).  When reference_id is empty this reduces to the previous
  // first-match-by-map-order behaviour.
  const typet *best_type = nullptr;
  const exprt *best_expr = nullptr;
  std::size_t best_score = 0;
  bool have = false;

  for(const auto &entry : type_map)
  {
    // N5008 [basic.scope.temp]: a nil-valued entry is a placeholder for a
    // template parameter that has NO binding in the current instantiation
    // context (e.g. the parameter of a sibling partial specialization whose
    // scope shares the reference's path).  It is not a live binding; choosing
    // it over a bound same-short-name parameter of an enclosing template
    // (the libstdc++ __strip_reference_wrapper primary-vs-partial-spec `_Tp`
    // during make_tuple's return-type elaboration) aborts the resolution
    // that the bound entry would have satisfied.
    if(entry.second.is_nil())
      continue;
    const std::string key = id2string(entry.first);
    if(!is_match(key))
      continue;
    const std::size_t score =
      ref.empty() ? 0 : common_scope_components(key, ref);
    if(!have || score > best_score)
    {
      have = true;
      best_score = score;
      best_type = &entry.second;
      best_expr = nullptr;
    }
    if(ref.empty())
      break; // preserve first-match behaviour when not disambiguating
  }
  for(const auto &entry : expr_map)
  {
    // skip placeholder (unbound) entries -- see the type_map loop above
    if(entry.second.is_nil())
      continue;
    const std::string key = id2string(entry.first);
    if(!is_match(key))
      continue;
    const std::size_t score =
      ref.empty() ? 0 : common_scope_components(key, ref);
    // Strict ">" keeps a type-parameter match ahead of an equally-scoped
    // non-type match.
    if(!have || score > best_score)
    {
      have = true;
      best_score = score;
      best_expr = &entry.second;
      best_type = nullptr;
    }
    if(ref.empty() && best_type == nullptr)
      break;
  }

  if(best_type != nullptr)
  {
    exprt e(ID_type);
    e.type() = *best_type;
    return e;
  }
  if(best_expr != nullptr)
    return *best_expr;
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

  // these should have been typechecked before.  A parameter pack need not be
  // the last template parameter: a class template partial specialization may
  // place it before further parameters, e.g.
  // `template <class R, class... A, class F> struct H<R(A...), F>` (the shape
  // of libstdc++'s _Function_handler).  Find the (single) pack at whatever
  // position it occupies.
  int pack_idx = -1;
  std::size_t n_packs = 0;
  for(std::size_t k = 0; k < template_parameters.size(); ++k)
    if(template_parameters[k].get_bool(ID_ellipsis))
    {
      if(pack_idx < 0)
        pack_idx = static_cast<int>(k);
      ++n_packs;
    }
  const bool has_pack = pack_idx >= 0;

  if(
    n_packs <= 1 && instance.size() != template_parameters.size() &&
    !(has_pack && instance.size() >= template_parameters.size() - 1))
  {
    return; // mismatched template arguments — skip
  }

  // Per C++ name-lookup rules, the parameters of the template
  // currently being instantiated SHADOW any same-named parameters
  // from a textually-enclosing template that is also currently
  // being instantiated.  CBMC keeps all enclosing template_map
  // entries alive across nested `instantiate_template` calls
  // (the saved-map mechanism captures and restores by COPY, so
  // entries from outer scopes coexist with the inner scope's
  // entries in `type_map` / `expr_map` / `pack_*_map`).  Without
  // shadowing, `template_mapt::apply`'s short-name suffix-match
  // can return the outer binding when an inner same-named
  // parameter exists, which produces wrong substitutions for
  // nested instantiations of unrelated class templates that
  // happen to share parameter names (e.g. both `__replace_first_arg`
  // and `allocator` having a parameter called `_Tp`).
  //
  // Shadow by removing any pre-existing entry whose short-name
  // suffix matches one of THIS template's parameters but whose
  // full identifier differs (so we don't drop our own to-be-set
  // entry).  The `cpp_saved_template_mapt` of the enclosing
  // `instantiate_template` will restore the removed entries when
  // this scope exits.
  {
    auto short_name = [](const irep_idt &id) -> std::string
    {
      const std::string s = id2string(id);
      auto p = s.rfind("::");
      return p != std::string::npos ? s.substr(p + 2) : s;
    };
    std::set<std::string> new_short_names;
    std::set<irep_idt> new_full_ids;
    for(const auto &p : template_parameters)
    {
      irep_idt pid =
        p.id() == ID_type ? p.type().get(ID_identifier) : p.get(ID_identifier);
      if(pid.empty())
        continue;
      new_full_ids.insert(pid);
      new_short_names.insert(short_name(pid));
    }
    auto shadow = [&](auto &m)
    {
      for(auto it = m.begin(); it != m.end();)
      {
        if(
          new_full_ids.count(it->first) == 0 &&
          new_short_names.count(short_name(it->first)) != 0)
          it = m.erase(it);
        else
          ++it;
      }
    };
    shadow(type_map);
    shadow(expr_map);
    shadow(pack_size_map);
    shadow(pack_args_map);
    shadow(pack_expr_map);
  }

  // N5008 [temp.param]/14: a member template's template-parameter-list may
  // contain MULTIPLE parameter packs when each is deducible from the
  // function parameters (e.g. std::pair's piecewise constructor
  // `template<class... _Args1, class... _Args2>
  //  pair(piecewise_construct_t, tuple<_Args1...>, tuple<_Args2...>)`).
  // The positional `instance` list cannot encode how its elements split
  // between the packs, so reconstructing pack bindings from it is ill-posed
  // -- the single-pack arithmetic below would bind the FIRST pack empty and
  // scalar-bind the second to the first pack's element, swapping the packs
  // in the instantiated signature.  Deduction has already recorded each
  // pack's elements in pack_args_map / pack_size_map under this template's
  // own parameter identifiers (which the shadowing above preserves: their
  // full ids are our own).  Bind only the non-pack parameters positionally,
  // consuming each pack's recorded element count from the flat list, and
  // keep the recorded pack bindings.
  if(n_packs > 1)
  {
    std::size_t arg_idx = 0;
    for(std::size_t p = 0;
        p < template_parameters.size() && arg_idx < instance.size();
        ++p)
    {
      if(template_parameters[p].get_bool(ID_ellipsis))
      {
        const irep_idt pid =
          template_parameters[p].id() == ID_type
            ? template_parameters[p].type().get(ID_identifier)
            : template_parameters[p].get(ID_identifier);
        const auto ps_it = pack_size_map.find(pid);
        if(ps_it != pack_size_map.end())
          arg_idx += ps_it->second;
        continue;
      }
      set(template_parameters[p], instance[arg_idx]);
      ++arg_idx;
    }
    return;
  }

  // Bind each parameter to its argument(s).  With a parameter pack at index
  // `pack_idx`, the parameters before the pack bind positionally from the
  // front, the pack absorbs the `pack_count` middle arguments, and the
  // parameters after the pack bind positionally from the back (shifted by
  // `pack_count - 1`).  Without a pack this is the plain 1:1 binding.
  const std::size_t nparams = template_parameters.size();
  const std::size_t nargs = instance.size();
  const std::size_t non_pack = has_pack ? nparams - 1 : nparams;
  // N5008 [temp.variadic]/5,8: a type parameter pack binds the run of
  // arguments not consumed by the non-pack parameters; `sizeof...` is its
  // element count (recorded below in pack_size_map/pack_args_map).
  //
  // CONFORMANCE NOTE (see doc/architectural/
  // cpp-frontend-review-2026-06-23-deduction-conformance.md, Gap G1):
  // `pack_count` is derived purely from the *number* of arguments supplied in
  // `instance`.  This is faithful only if the caller has already applied
  // [temp.arg.explicit]/4 Note 1 -- "a trailing template parameter pack not
  // otherwise deduced will be deduced as an empty sequence".  If an explicitly
  // but partially specialized function template (e.g. `__get_helper<0>` with a
  // trailing, non-deduced `_Tail`) reaches here with a spurious extra trailing
  // argument bled in from an enclosing instantiation, `pack_count` is
  // over-counted and the pack is wrongly sized non-empty.  The trailing pack
  // must be pinned to empty *before* this count is taken; build() cannot
  // recover it here.
  const std::size_t pack_count =
    has_pack && nargs >= non_pack ? nargs - non_pack : 0;
  for(std::size_t p = 0; p < nparams; ++p)
  {
    // A parameter pack must not be scalar-bound to its first argument here.
    // For a *type* pack that records type_map[Pack] = <first element>; for a
    // *non-type* pack that records expr_map[Pack] = <first value>.  Either
    // way it then collapses pack expansions and `sizeof...(Pack)` to a single
    // element.  Packs are bound below via pack_size_map and pack_args_map (type
    // packs) / pack_expr_map (non-type packs), plus a single-element
    // convenience entry, per [temp.variadic]/5,8.
    const bool is_pack = static_cast<int>(p) == pack_idx;
    if(is_pack)
      continue;
    // The argument index for this parameter: parameters at or before the pack
    // align from the front; parameters after the pack are shifted by the
    // number of extra pack elements.
    const std::size_t arg_idx =
      (!has_pack || static_cast<int>(p) <= pack_idx) ? p : p + pack_count - 1;
    if(arg_idx < nargs)
      set(template_parameters[p], instance[arg_idx]);
  }

  // Record pack sizes for sizeof...(Pack)
  if(has_pack)
  {
    const auto &pack_param = template_parameters[pack_idx];
    irep_idt pack_id = pack_param.id() == ID_type
                         ? pack_param.type().get(ID_identifier)
                         : pack_param.get(ID_identifier);
    std::size_t pack_sz = pack_count;

    // The pack absorbs the `pack_count` arguments starting at `pack_idx`
    // (the parameters after the pack bind to the trailing arguments).
    std::vector<typet> pack_types;
    for(std::size_t j = static_cast<std::size_t>(pack_idx);
        j < static_cast<std::size_t>(pack_idx) + pack_count && j < nargs;
        ++j)
    {
      if(instance[j].id() == ID_type)
      {
        // Recognize the `empty_typet()` sentinel used by
        // `elaborate_class_template`'s spec-matching path
        // (cpp_instantiate_template.cpp) to encode "pack matched zero
        // elements" in `guessed_args` (an unassigned pack param has no
        // natural representation in `cpp_template_args_tct`'s
        // arguments list, which is positional).  Treat it as a
        // zero-length pack rather than as a literal `void`-typed
        // pack element.
        if(instance[j].type().id() == ID_empty)
        {
          if(pack_sz > 0)
            --pack_sz;
          continue;
        }
        pack_types.push_back(instance[j].type());
      }
    }
    // N5008 [temp.variadic]: collect a NON-type pack's element VALUES (the
    // value analogue of pack_types), so `Foo<T...>` over it can be expanded to
    // the concrete constants.  Now that a non-type pack is no longer
    // scalar-bound in expr_map (see the gate above), this is its only binding.
    std::vector<exprt> pack_exprs;
    for(std::size_t j = static_cast<std::size_t>(pack_idx);
        j < static_cast<std::size_t>(pack_idx) + pack_count && j < nargs;
        ++j)
    {
      if(instance[j].id() != ID_type)
        pack_exprs.push_back(instance[j]);
    }
    pack_size_map[pack_id] = pack_sz;
    if(!pack_types.empty())
    {
      pack_args_map[pack_id] = std::move(pack_types);
      // Per [temp.variadic]/7: for single-element packs, also add
      // the type to type_map so template_map.apply() can substitute.
      if(pack_args_map[pack_id].size() == 1)
        type_map[pack_id] = pack_args_map[pack_id].front();
    }
    else if(!pack_exprs.empty())
    {
      // Non-type parameter pack: bind its element VALUES (the value analogue
      // of the type-pack branch above), per [temp.variadic]/5,8.  A
      // single-element non-type pack also gets a scalar expr_map convenience
      // entry, mirroring the type_map convenience.
      pack_expr_map[pack_id] = std::move(pack_exprs);
      if(pack_expr_map[pack_id].size() == 1)
        expr_map[pack_id] = pack_expr_map[pack_id].front();
      pack_args_map.erase(pack_id);
      type_map.erase(pack_id);
    }
    else
    {
      // The pack binds to zero elements.  When a variadic template recurses
      // with the SAME pack parameter name -- a variadic partial
      // specialization whose base names the same template,
      // `And<B1, Bn...> : bc<B1::value && And<Bn...>::value>` -- this
      // (inner) instance's empty `Bn` shares its identifier with the
      // enclosing instance's non-empty `Bn`, and `build` runs against the
      // map inherited from that enclosing instantiation.  Since an empty
      // pack records no `pack_args_map` entry, the enclosing `Bn = [X]`
      // would otherwise survive and make `And<Bn...>` expand to the
      // enclosing instance, recursing onto itself.  Erase any inherited
      // binding so the empty pack expands to zero arguments ([temp.variadic]).
      pack_args_map.erase(pack_id);
      type_map.erase(pack_id);
      pack_expr_map.erase(pack_id);
      expr_map.erase(pack_id);
    }
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

    // Skip template_parameter_symbol_typet values with numeric
    // scope IDs — these are unresolved template template parameters.
    if(tmp.id() == ID_template_parameter_symbol_type)
    {
      const irep_idt &ttp_id =
        to_template_parameter_symbol_type(tmp).get_identifier();
      std::string ttp_str = id2string(ttp_id);
      auto ttp_pos = ttp_str.rfind("::");
      std::string ttp_suffix =
        ttp_pos != std::string::npos ? ttp_str.substr(ttp_pos + 2) : ttp_str;
      if(!ttp_suffix.empty() && std::isdigit(ttp_suffix[0]))
      {
        // Don't store — the value is an unresolved scope ID.
        // A later set() call will provide the correct value.
      }
      else
        type_map[identifier] = tmp;
    }
    else
      type_map[identifier] = tmp;
  }
  else
  {
    // must be non-type

    if(value.id() == ID_type)
    {
      // Non-type template parameter receiving a value of id
      // `ID_type`: this can occur during eager constexpr-eval when
      // a sub-instantiation is reached before the call's
      // arguments have been adjusted to the parameter's
      // value-shape (see [temp.deduct]/8 — substitution failure is
      // not an error in immediate context).  Per the standard's
      // SFINAE rule, the right behaviour is a soft failure: leave
      // the binding unset; downstream lookup will produce a
      // regular diagnostic at the use site if the binding is
      // actually needed.  Replacing the prior UNREACHABLE here
      // avoids aborting on legitimate SFINAE branches that show up
      // once class-template constexpr methods get eagerly
      // type-checked.
      return;
    }

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

    // [temp.deduct]/2: template argument deduction starts from a clean
    // slate -- the parameters being deduced have no prior assignment.
    // A parameter pack additionally records its element list/size in
    // pack_args_map/pack_size_map; these must be cleared too.  Otherwise,
    // when a variadic template recurses with the SAME pack parameter name
    // -- a variadic partial specialization whose base names the same
    // template, `And<B1, Bn...> : ... && And<Bn...>::value` -- the inner
    // deduction would inherit the enclosing instance's pack arguments
    // (`Bn = [X]`) instead of deducing an empty pack, so the recursive
    // `And<Bn...>` would re-expand to the enclosing instance and recurse
    // onto itself, failing to resolve.
    //
    // Erasing the pack maps here is also what gives a *trailing* pack its
    // [temp.arg.explicit]/4 Note 1 default of an empty sequence -- but only
    // IMPLICITLY: the pack stays empty solely because no later step supplies
    // an argument for it.  That implicit default is defeated if argument
    // assembly bleeds in a spurious trailing element (see Gap G1 in
    // doc/architectural/cpp-frontend-review-2026-06-23-deduction-conformance.md
    // and template_mapt::build's pack_count note).
    const irep_idt &pid =
      t.id() == ID_type ? t.type().get(ID_identifier) : t.get(ID_identifier);
    pack_args_map.erase(pid);
    pack_size_map.erase(pid);
    pack_expr_map.erase(pid);
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

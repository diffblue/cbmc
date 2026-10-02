/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/symbol_table_base.h>

#include <ansi-c/padding.h>

#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"

#include <algorithm>
#include <functional>
#include <set>

void cpp_typecheckt::drop_empty_pack_template_args(irept &name)
{
  // Guarded by a non-empty pack_size_map so the primary template definition
  // (no instantiation context) is untouched.
  if(template_map.pack_size_map.empty())
    return;

  const auto classify_pack_refs =
    [&](const irept &arg, bool &refs_empty, bool &refs_nonempty)
  {
    std::function<void(const irept &)> walk = [&](const irept &n)
    {
      if(n.id() == ID_name)
      {
        const std::string nm = id2string(n.get(ID_identifier));
        for(const auto &e : template_map.pack_size_map)
        {
          const std::string key = id2string(e.first);
          const auto p = key.rfind("::");
          const std::string suffix =
            p != std::string::npos ? key.substr(p + 2) : key;
          if(suffix == nm)
          {
            if(e.second == 0)
              refs_empty = true;
            else
              refs_nonempty = true;
          }
        }
      }
      for(const auto &sub : n.get_sub())
        walk(sub);
      for(const auto &ns : n.get_named_sub())
        walk(ns.second);
    };
    walk(arg);
  };

  for(auto &sub : name.get_sub())
  {
    if(sub.id() != ID_template_args)
      continue;
    irept::subt &args = sub.add(ID_arguments).get_sub();
    args.erase(
      std::remove_if(
        args.begin(),
        args.end(),
        [&](const irept &arg)
        {
          const bool is_expansion = arg.get_bool(ID_ellipsis) ||
                                    arg.find(ID_type).get_bool(ID_ellipsis);
          if(!is_expansion)
            return false;
          bool refs_empty = false, refs_nonempty = false;
          classify_pack_refs(arg, refs_empty, refs_nonempty);
          return refs_empty && !refs_nonempty;
        }),
      args.end());
  }
}

void cpp_typecheckt::typecheck_compound_bases(struct_typet &type)
{
  std::set<irep_idt> vbases;

  irep_idt default_class_access = type.default_access();

  irept::subt &bases_irep=type.add(ID_bases).get_sub();

  struct resolved_baset
  {
    const symbolt *symbol;
    irep_idt access;
    bool is_virtual;
  };
  std::vector<resolved_baset> resolved_bases;

  for(auto &base : bases_irep)
  {
    cpp_namet &name = static_cast<cpp_namet &>(base.add(ID_name));

    // N5008 [temp.variadic]/7: a base-specifier template argument that is a
    // pack expansion (`X...`) over a pack empty in this instantiation expands
    // to an empty argument list, e.g. `Empty<_Tail...>` -> `Empty<>`.
    drop_empty_pack_template_args(name);

    // Apply template_map to substitute template parameters in the
    // base class template arguments (e.g., _Tp in integral_constant<bool,
    // noexcept(declval<_Tp>().~_Tp())>). Only apply when both type_map
    // and expr_map are non-empty (indicating a partial specialization
    // with both type and non-type parameters).
    if(!template_map.type_map.empty())
    {
      // Check if any template arg contains a template parameter
      // from the current type_map before applying substitution.
      bool has_param = false;
      for(const auto &sub : name.get_sub())
      {
        if(sub.id() != ID_template_args)
          continue;
        const auto &args = sub.find(ID_arguments).get_sub();
        for(const auto &arg : args)
        {
          // Check recursively for cpp_name nodes that match type_map
          std::function<bool(const irept &)> contains_param =
            [&](const irept &node) -> bool
          {
            if(node.id() == ID_name)
            {
              irep_idt id = node.get(ID_identifier);
              for(const auto &entry : template_map.type_map)
              {
                const std::string &key = id2string(entry.first);
                auto p = key.rfind("::");
                std::string suffix =
                  p != std::string::npos ? key.substr(p + 2) : key;
                if(suffix == id2string(id))
                  return true;
              }
            }
            for(const auto &s : node.get_sub())
              if(contains_param(s))
                return true;
            for(const auto &n : node.get_named_sub())
              if(contains_param(n.second))
                return true;
            return false;
          };
          if(contains_param(arg))
          {
            has_param = true;
            break;
          }
        }
        if(has_param)
          break;
      }
      if(has_param)
      {
        // N5008 [temp.variadic]/5: substitute the WHOLE template-id, not
        // each argument on its own.  A pack expansion `A...` is a single
        // argument node that must become one argument per pack element;
        // applying the map per argument could only replace it by the
        // pack's scalar (first) element, so `RO<F(A...)> : impl<F, A...>`
        // (libstdc++'s `result_of<_Functor(_ArgTypes...)> :
        // __invoke_result<_Functor, _ArgTypes...>`) derived from
        // impl<F, A0> whenever the pack was deduced from a function-type
        // pattern with two or more parameters -- result_of<F&(int&, int&)>
        // then had no `type` and every std::bind result type failed.
        typet name_type;
        static_cast<irept &>(name_type) = static_cast<const irept &>(name);
        template_map.apply(name_type);
        if(name_type.id() == ID_cpp_name)
          static_cast<irept &>(name) = static_cast<const irept &>(name_type);
      }
    }

    // C++11: decltype(expr) as base specifier
    exprt base_symbol_expr;
    if(name.get_sub().size() == 1 && name.get_sub().front().id() == ID_decltype)
    {
      typet t = static_cast<const typet &>(name.get_sub().front());
      typecheck_type(t);
      base_symbol_expr = type_exprt(t);
    }
    else
    {
      // N5008 [class.derived]/2 + [temp.inst]/3: during template
      // instantiation, failure to resolve ONE base-specifier (e.g. the
      // `__is_destructible_impl<...>::type` SFINAE machinery of a
      // libstdc++ trait) must not abandon the OTHER bases: the sibling
      // bases are independently valid, and dropping them all left e.g.
      // std::optional<std::string> without its _Optional_base -- its
      // constructors' member initializers then crashed the front end on
      // a derived-to-base cast between "unrelated" structs
      // (make_ptr_typecast precondition).  Recover per base: nil this
      // entry (the same graceful degradation the non-throwing failure
      // paths below use) and continue with the next.  User-code base
      // errors outside instantiation still throw.
      // N5008 [temp.names]/8 + [temp.res.general]: within an
      // instantiated declaration a template parameter denotes its bound
      // argument.  When the base-specifier is a BARE template parameter
      // (`renamedt<T> : T`) and the active template map binds it, use
      // the binding directly: scope-based resolution of the parameter
      // name fails when the instance is completed from a context where
      // the original template scope chain is not entered (the
      // incomplete-to-complete swap; the map there is built from the
      // instance's recorded arguments).
      bool base_from_map = false;
      if(name.get_sub().size() == 1 && name.get_sub().front().id() == ID_name)
      {
        const std::string id =
          id2string(name.get_sub().front().get(ID_identifier));
        for(const auto &te : template_map.type_map)
        {
          const std::string key = id2string(te.first);
          const auto pos = key.rfind("::");
          if(
            (pos != std::string::npos ? key.substr(pos + 2) : key) == id &&
            te.second.id() == ID_struct_tag)
          {
            base_symbol_expr = type_exprt(te.second);
            base_from_map = true;
            break;
          }
        }
      }
      if(base_from_map)
      {
        // resolved via the template map
      }
      else if(instantiation_stack.empty())
      {
        base_symbol_expr = resolve(
          name, cpp_typecheck_resolvet::wantt::TYPE, cpp_typecheck_fargst());
      }
      else
      {
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        try
        {
          base_symbol_expr = resolve(
            name, cpp_typecheck_resolvet::wantt::TYPE, cpp_typecheck_fargst());
        }
        catch(...)
        {
          get_message_handler().set_message_count(
            messaget::M_ERROR, errors_before);
          base = get_nil_irep();
          continue;
        }
      }
    }

    if(base_symbol_expr.id()!=ID_type)
    {
      error().source_location=name.source_location();
      error() << "expected type as struct/class base" << eom;
      throw 0;
    }

    // N5008 [class.derived.general]/2: "The class-or-decltype shall denote
    // a (possibly cv-qualified) class type that is not an incompletely
    // defined class" -- a class is incomplete in its own base-specifier-list
    // (`struct X : X').  Accepting it
    // made the type checker recurse without bound (SIGSEGV).
    // Only the class itself is checked: treating every base whose
    // elaboration is in progress as incomplete also rejected well-formed
    // libc++ <ostream> code (the body of basic_ostream::sentry::sentry).
    if(
      base_symbol_expr.type().id() == ID_struct_tag &&
      to_struct_tag_type(base_symbol_expr.type()).get_identifier() ==
        type.get(ID_name))
    {
      error().source_location = name.source_location();
      error() << "base class '" << to_string(base_symbol_expr.type())
              << "' is incomplete: a class cannot be derived from itself"
              << eom;
      throw 0;
    }

    // elaborate any class template instances given as bases
    elaborate_class_template(base_symbol_expr.type());

    if(base_symbol_expr.type().id() != ID_struct_tag)
    {
      // Base type resolution failed (e.g., template instantiation
      // failed in system headers). Remove this base and continue.
      base = get_nil_irep();
      continue;
    }

    const symbolt &base_symbol =
      lookup(to_struct_tag_type(base_symbol_expr.type()));

    if(base_symbol.type.id() != ID_struct)
    {
      base = get_nil_irep();
      continue;
    }

    if(to_struct_type(base_symbol.type).is_incomplete())
    {
      // N5008 [class.derived.general]/2 requires a complete base; this
      // point of instantiation was reached EAGERLY from a context that
      // per [temp.inst]/1 does not require the specialization's
      // definition (e.g. the return type of a function DECLARATION,
      // `renamedt<ssa_exprt> f(const ssa_exprt&);` with ssa_exprt still
      // incomplete).  Drop the base to keep going, but MARK the class:
      // a later use after the argument type is completed is a new,
      // valid point of instantiation ([temp.point]) and must
      // re-elaborate rather than reuse this degenerate layout.
      type.set("#dropped_incomplete_base", base_symbol.name);
      base = get_nil_irep();
      continue;
    }

    // N5008 [class.mi]/3: "A class shall not be specified as a direct base
    // class of a derived class more than once" (it can be an indirect base
    // more than once, and a direct and an indirect base)
    for(const auto &resolved : resolved_bases)
    {
      if(resolved.symbol->name == base_symbol.name)
      {
        error().source_location = name.source_location();
        error() << "duplicate direct base class '" << base_symbol.pretty_name
                << "'" << eom;
        throw 0;
      }
    }

    bool virtual_base = base.get_bool(ID_virtual);
    irep_idt class_access = base.get(ID_protection);

    if(class_access.empty())
      class_access = default_class_access;

    base_symbol_expr.id(ID_base);
    base_symbol_expr.set(ID_access, class_access);

    if(virtual_base)
      base_symbol_expr.set(ID_virtual, true);

    base.swap(base_symbol_expr);

    // Add base scopes as parents to the current scope
    cpp_scopes.current_scope().add_secondary_scope(
      static_cast<cpp_scopet &>(*cpp_scopes.id_map[base_symbol.name]));

    // the base subobject is laid out below, once every base is resolved:
    // Itanium C++ ABI 2.4 II.1 puts the PRIMARY base (the first non-virtual
    // dynamic base in declaration order) at offset 0, before the other bases,
    // whatever its position in the base-specifier-list
    resolved_bases.push_back({&base_symbol, class_access, virtual_base});
  }

  // lay out the base subobjects: primary base first, then the others in
  // declaration order.  The bases() of the type keep declaration order (the
  // order of construction, N5008 [class.base.init]/13).
  {
    std::size_t primary_index = resolved_bases.size();
    for(std::size_t i = 0; i < resolved_bases.size(); ++i)
    {
      if(
        !resolved_bases[i].is_virtual &&
        !vtable_pointer_component(resolved_bases[i].symbol->name).empty())
      {
        primary_index = i;
        break;
      }
    }
    std::vector<std::size_t> layout_order;
    if(primary_index < resolved_bases.size())
      layout_order.push_back(primary_index);
    // Itanium C++ ABI 2.4 II.3: the virtual bases are not part of the
    // non-virtual part; they are laid out once each after the class's own
    // members (append_virtual_bases, from typecheck_compound_body)
    for(std::size_t i = 0; i < resolved_bases.size(); ++i)
      if(i != primary_index && !resolved_bases[i].is_virtual)
        layout_order.push_back(i);

    for(const std::size_t i : layout_order)
    {
      const symbolt &base_symbol = *resolved_bases[i].symbol;
      const irep_idt class_access = resolved_bases[i].access;
      const bool virtual_base = resolved_bases[i].is_virtual;
      const struct_typet &base_struct_type = to_struct_type(base_symbol.type);

      // Itanium C++ ABI 2.4 (base subobject layout, approximated on the
      // flattened components): the direct base subobject starts at the next
      // offset suitably aligned for the BASE (add_padding reads the marker on
      // its first component), and a base that is not a POD for the purpose of
      // layout does not keep its tail padding -- the derived class's members
      // may start in it (dsize(B) < sizeof(B)).  A POD base keeps sizeof(B).
      const std::size_t first_new = to_struct_type(type).components().size();
      add_base_components(
        base_struct_type, class_access, type, vbases, virtual_base);
      auto &components = to_struct_type(type).components();
      // the marker goes on the first component that occupies storage (the
      // layout ignores member functions, static members and member types)
      std::size_t first_storage = first_new;
      while(
        first_storage < components.size() &&
        (components[first_storage].type().id() == ID_code ||
         components[first_storage].get_bool(ID_is_static) ||
         components[first_storage].get_bool(ID_is_type) ||
         (components[first_storage].type().id() == ID_c_bit_field &&
          to_c_bit_field_type(components[first_storage].type()).get_width() ==
            0)))
      {
        ++first_storage;
      }
      const namespacet ns(symbol_table);
      mp_integer base_alignment = alignment(base_struct_type, ns);
      if(first_storage >= components.size())
      {
        // an EMPTY base (its padding was dropped): no subobject to place, but
        // an over-aligned one (`struct alignas(16) E {};') still aligns the
        // derived class -- record it as the class's alignment requirement.
        // (g++ and clang do not cap it under `#pragma pack', unlike a
        // non-empty base's alignment.)
        const exprt &current =
          static_cast<const exprt &>(type.find(ID_C_alignment));
        const auto current_value = current.is_nil()
                                     ? std::optional<mp_integer>{}
                                     : numeric_cast<mp_integer>(current);
        if(
          base_alignment > 1 &&
          !(current_value.has_value() && *current_value >= base_alignment))
        {
          type.add(ID_C_alignment) = from_integer(base_alignment, size_type());
        }
      }
      else
      {
        // `#pragma pack(n)' around the derived class definition caps the
        // base subobject's alignment as well (GCC)
        const auto pack = numeric_cast<mp_integer>(
          static_cast<const exprt &>(type.find(ID_C_pragma_pack)));
        if(pack.has_value() && *pack > 0 && *pack < base_alignment)
          base_alignment = *pack;
        components[first_storage].set(
          ID_C_base_alignment, integer2string(base_alignment));
        if(!cpp_is_pod(base_struct_type))
        {
          while(components.size() > first_new &&
                components.back().get_is_padding() &&
                components.back().type().id() != ID_c_bit_field)
          {
            components.pop_back();
          }
        }
      }
    }
  }

  // Remove bases that were invalidated (set to nil) during validation.
  bases_irep.erase(
    std::remove_if(
      bases_irep.begin(),
      bases_irep.end(),
      [](const irept &b) { return b.is_nil(); }),
    bases_irep.end());

  // The virtual bases' members, so that name lookup and the detection of
  // overriders of their virtual functions see them while the class's own
  // members are processed; typecheck_compound_body moves them behind the
  // own members afterwards, where the layout places them.
  append_virtual_bases(type, vbases);
}

void cpp_typecheckt::append_virtual_bases(
  struct_typet &type,
  std::set<irep_idt> &vbases)
{
  // Itanium C++ ABI 2.4 II.3: after the non-virtual part (bases and own
  // members) come the virtual bases, once each, in inheritance graph order
  // (depth-first, left to right, a class before the virtual bases of its own
  // bases -- get_virtual_bases produces that order).  Each is placed like a
  // direct base: at the next offset aligned for it, without its tail padding
  // when it is not a POD for the purpose of layout.
  std::list<irep_idt> vbase_ids;
  get_virtual_bases(type, vbase_ids);
  if(vbase_ids.empty())
    return;

  // the access a virtual base's members have in this class: that of the
  // direct base-specifier naming it, public when it is only indirect
  std::map<irep_idt, irep_idt> direct_access;
  for(const auto &b : type.bases())
  {
    if(b.get_bool(ID_virtual) && b.type().id() == ID_struct_tag)
    {
      direct_access[to_struct_tag_type(b.type()).get_identifier()] =
        b.get(ID_access);
    }
  }

  const namespacet ns(symbol_table);
  auto &components = type.components();

  for(const irep_idt &vbase_id : vbase_ids)
  {
    const symbolt *vbase_symbol = symbol_table.lookup(vbase_id);
    if(vbase_symbol == nullptr || vbase_symbol->type.id() != ID_struct)
      continue;
    const struct_typet &vbase_struct = to_struct_type(vbase_symbol->type);

    const auto access_it = direct_access.find(vbase_id);
    const irep_idt access =
      access_it != direct_access.end() ? access_it->second : ID_public;

    // add_base_components copies the non-virtual part of the base (it does
    // not descend into virtual bases and skips their components); a class
    // that is a non-virtual base of it and of another base is a separate
    // subobject in each ([class.mi]/4)
    const std::size_t first_new = components.size();
    add_base_components(vbase_struct, access, type, vbases, true);

    for(std::size_t i = first_new; i < components.size(); ++i)
      components[i].set(ID_C_virtual_base, vbase_id);

    std::size_t first_storage = first_new;
    while(first_storage < components.size() &&
          (components[first_storage].type().id() == ID_code ||
           components[first_storage].get_bool(ID_is_static) ||
           components[first_storage].get_bool(ID_is_type) ||
           (components[first_storage].type().id() == ID_c_bit_field &&
            to_c_bit_field_type(components[first_storage].type()).get_width() ==
              0)))
    {
      ++first_storage;
    }
    if(first_storage < components.size())
    {
      // `#pragma pack(n)' around the class definition caps the virtual
      // base's alignment as it caps a non-virtual base's (GCC)
      mp_integer base_alignment = alignment(vbase_struct, ns);
      const auto pack = numeric_cast<mp_integer>(
        static_cast<const exprt &>(type.find(ID_C_pragma_pack)));
      if(pack.has_value() && *pack > 0 && *pack < base_alignment)
        base_alignment = *pack;
      components[first_storage].set(
        ID_C_base_alignment, integer2string(base_alignment));
      if(!cpp_is_pod(vbase_struct))
      {
        while(components.size() > first_new &&
              components.back().get_is_padding() &&
              components.back().type().id() != ID_c_bit_field)
        {
          components.pop_back();
        }
      }
    }
  }
}

void cpp_typecheckt::add_base_components(
  const struct_typet &from,
  const irep_idt &access,
  struct_typet &to,
  std::set<irep_idt> &vbases,
  bool is_virtual)
{
  const irep_idt &from_name = from.get(ID_name);

  // N5008 [class.mi]/4: a virtual base class is ONE subobject of the most
  // derived object, however often it is named
  if(is_virtual && vbases.find(from_name) != vbases.end())
    return;

  // ... whereas each distinct occurrence of a non-virtual base class in the
  // class lattice is a distinct subobject ([class.mi]/4-5): `struct D : B,
  // C' with `B : A' and `C : A' has two A subobjects, one in B and one in C.
  if(is_virtual)
    vbases.insert(from_name);

  // Access of a base member, as inherited through an edge with the
  // given protection ([class.access.base]/1), preserving inaccessible
  // (noaccess) members.
  auto inherited_access =
    [](const irep_idt &edge, const irep_idt &member) -> irep_idt
  {
    if(member == ID_noaccess)
      return ID_noaccess;
    if(edge == ID_public)
      return member == ID_private ? ID_noaccess : member;
    // protected or private inheritance
    return member == ID_private ? ID_noaccess : ID_private;
  };

  // An EMPTY base class has no storage member of its own -- only the byte
  // that makes it a nonzero-sized complete object ([class]/4).  As a base
  // subobject it may have zero size ([intro.object]/9; the Itanium ABI's
  // empty base optimisation): drop its padding on flattening.
  bool base_is_empty = true;
  for(const auto &c : from.components())
  {
    if(
      c.type().id() != ID_code && !c.get_bool(ID_is_static) &&
      !c.get_bool(ID_is_type) && !c.get_is_padding() &&
      c.get(ID_C_virtual_base).empty() &&
      !(c.type().id() == ID_c_bit_field &&
        to_c_bit_field_type(c.type()).get_width() == 0))
    {
      base_is_empty = false;
      break;
    }
  }

  // component names must be unique within a struct type
  std::set<irep_idt> names;
  for(const auto &c : to.components())
    names.insert(c.get_name());

  // The base subobject is `from's non-virtual part as `from' laid it out
  // (Itanium C++ ABI 2.4): its own members and, flattened already, its
  // non-virtual bases, with its padding between them.  Copy it, recording
  // for each component the path of base classes through which it is
  // reached from `to' (subobject_path: the subobject it belongs to).
  struct_typet::componentst &dest_c = to.components();
  for(const auto &c : from.components())
  {
    if(base_is_empty && c.get_is_padding())
      continue;

    // `from's own virtual bases (and the padding in front of them) are not
    // in its non-virtual part; they are laid out once, by the most derived
    // class (append_virtual_bases)
    if(!c.get(ID_C_virtual_base).empty())
      continue;

    struct_typet::componentt component = c;
    component.set(ID_from_base, true);
    component.set_access(inherited_access(access, c.get_access()));

    // a member of a PACKED base keeps the base's packed layout in the
    // derived class (padding.cpp reads the mark; `struct P { char c; long
    // l; } __attribute__((packed)); struct D : P { int m; }' has m at 12)
    if(from.get_bool(ID_C_packed))
      component.set(ID_C_packed, true);

    irept::subt path;
    path.push_back(irept{from_name});
    for(const auto &step : c.find(ID_C_subobject_path).get_sub())
      path.push_back(step);
    component.add(ID_C_subobject_path).get_sub() = std::move(path);

    // A padding component of the base's layout is named by its index in
    // the base (`$pad2'); two bases contribute clashing names, and the
    // derived class's own padding may want the same index.
    if(component.get_is_padding())
    {
      component.set_name(
        id2string(component.get_name()) + "$b" + std::to_string(dest_c.size()));
    }
    // A member function, static data member or member type names one
    // entity however many subobjects of its class there are ([class.static],
    // [class.member.lookup]/5.3: the same declaration set); an entry already
    // present is that entity (reached through another base, or an
    // inherited constructor), and it is not duplicated.
    else if(
      names.count(component.get_name()) != 0 &&
      (component.type().id() == ID_code || component.get_bool(ID_is_static) ||
       component.get_bool(ID_is_type)))
    {
      continue;
    }
    // A non-static data member of a base class that occurs more than once
    // in the lattice (the second A in `D : B, C') is storage of a distinct
    // subobject: it keeps its declared name for lookup (#base_name), and
    // its component name is made unique from the subobject path.  The first
    // occurrence keeps its name.
    else if(names.count(component.get_name()) != 0)
    {
      std::string unique = id2string(component.get_name()) + "@";
      for(const auto &step : component.find(ID_C_subobject_path).get_sub())
        unique += "/" + id2string(step.id());
      std::string candidate = unique;
      for(std::size_t n = 1; names.count(candidate) != 0; ++n)
        candidate = unique + "#" + std::to_string(n);
      component.set_name(candidate);
    }
    names.insert(component.get_name());
    dest_c.push_back(std::move(component));
  }
}

/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>

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
  std::set<irep_idt> bases;
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
    for(std::size_t i = 0; i < resolved_bases.size(); ++i)
      if(i != primary_index)
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
        base_struct_type, class_access, type, bases, vbases, virtual_base);
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

  if(!vbases.empty())
  {
    // add a flag to determine
    // if this is the most-derived-object.
    // The flag is a BYTE-wide c_bool, not a 1-bit boolean: layout
    // offsets are computed bytewise (member_offset/member_offset_expr
    // refuse structs whose bit-field run is not byte-padded), and the
    // front end deliberately does not run add_padding() on classes
    // with bases -- a 1-bit flag made the byte offset of EVERY
    // subsequent member unknown, so pointer checks rejected ordinary
    // member writes in virtual-base classes ("pointer outside object
    // bounds in this->d") and goto-symex aborted on
    // build_object_descriptor_rec (std::ofstream construction).
    struct_typet::componentt most_derived(
      cpp_scopes.current_scope().prefix + "::" + "@most_derived",
      c_bool_type());

    most_derived.set_access(ID_public);
    most_derived.set_base_name("@most_derived");
    most_derived.set_pretty_name("@most_derived");
    most_derived.add_source_location()=type.source_location();
    put_compound_into_scope(most_derived);

    to_struct_type(type).components().push_back(most_derived);
  }
}

void cpp_typecheckt::add_base_components(
  const struct_typet &from,
  const irep_idt &access,
  struct_typet &to,
  std::set<irep_idt> &bases,
  std::set<irep_idt> &vbases,
  bool is_virtual)
{
  const irep_idt &from_name = from.get(ID_name);

  if(is_virtual && vbases.find(from_name)!=vbases.end())
    return;

  if(bases.find(from_name)!=bases.end())
  {
    error().source_location=to.source_location();
    error() << "non-virtual base class " << from_name
            << " inherited multiple times" << eom;
    throw 0;
  }

  bases.insert(from_name);

  if(is_virtual)
    vbases.insert(from_name);

  // where this base subobject starts in `to' (see the copy loop below)
  const std::size_t first_of_from = to.components().size();

  // look at the the parents of the base type
  for(const auto &b : from.bases())
  {
    // Skip bases with invalid types from failed template instantiations.
    if(static_cast<const exprt &>(b).type().id() != ID_struct_tag)
      continue;

    irep_idt sub_access = b.get(ID_access);

    if(access==ID_private)
      sub_access=ID_private;
    else if(access==ID_protected && sub_access!=ID_private)
      sub_access=ID_protected;

    const symbolt &symb = lookup(b.type());

    if(symb.type.id() != ID_struct)
      continue;

    const bool is_virtual_base = b.get_bool(ID_virtual);

    // recursive call
    const std::size_t before = to.components().size();
    add_base_components(
      to_struct_type(symb.type),
      sub_access,
      to,
      bases,
      vbases,
      is_virtual_base);

    // As for a direct base (typecheck_compound_bases): an indirect base that
    // is not a POD for the purpose of layout does not keep its tail padding
    // -- `from' laid its own members and further bases out in it (Itanium
    // C++ ABI 2.4: dsize(B) < sizeof(B)), and `from's copy of that padding
    // has already been dropped.  Keeping it here shifted every later
    // component of `from' (`U : T', `T : P, Q': P's tail padding survived in
    // U next to T's own alignment padding, putting Q's virtual pointer on a
    // misaligned offset and every later member 4 bytes off).
    if(!cpp_is_pod(symb.type))
    {
      auto &dest = to.components();
      while(dest.size() > before && dest.back().get_is_padding() &&
            dest.back().type().id() != ID_c_bit_field)
      {
        dest.pop_back();
      }
    }
  }

  // add the components
  struct_typet::componentst &dest_c=to.components();
  // The recursion above appended the components of `from's own bases; the
  // components `from' adds itself are inserted at their position within
  // `from's layout (`from' has been laid out: its padding sits between and
  // after its base subobjects, e.g. after an empty-typed member of its first
  // base and before its second base -- appending it at the end put the
  // padding after the second base's pointer, so a byte-offset access hit
  // the wrong bytes).  `cursor' walks `from.components()' and `dest_c' in
  // step.
  std::size_t cursor = first_of_from;

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
      !(c.type().id() == ID_c_bit_field &&
        to_c_bit_field_type(c.type()).get_width() == 0))
    {
      base_is_empty = false;
      break;
    }
  }

  for(const auto &c : from.components())
  {
    if(base_is_empty && c.get_is_padding())
      continue;

    const irep_idt new_access = inherited_access(access, c.get_access());

    if(c.get_bool(ID_from_base))
    {
      // The member is already flattened into `to` from its declaring
      // class via the recursion above.  Propagate its access as seen in
      // the immediate base `from` instead of keeping the declaring
      // class's access: an intermediate base may have changed it with a
      // using-declaration ([namespace.udecl]/19), e.g. binary_exprt's
      // public `using exprt::op0;` republishing the protected op0.
      for(std::size_t i = 0; i < dest_c.size(); ++i)
      {
        auto &d = dest_c[i];
        if(d.get_bool(ID_from_base) && d.get_name() == c.get_name())
        {
          d.set_access(new_access);
          // `from' marked the first component of each of its direct base
          // subobjects with the base's alignment (typecheck_compound_bases);
          // the recursion above copied the component from the base's own
          // type, which carries no such mark: propagate it, or the subobject
          // is not aligned in `to'.
          if(
            c.find(ID_C_base_alignment).is_not_nil() &&
            d.find(ID_C_base_alignment).is_nil())
          {
            d.set(ID_C_base_alignment, c.get(ID_C_base_alignment));
          }
          if(i >= first_of_from)
            cursor = i + 1;
        }
      }
      continue;
    }

    // copy the component, at its position within `from's layout
    auto inserted = dest_c.insert(dest_c.begin() + cursor, c);
    ++cursor;

    // now twiddle the copy
    struct_typet::componentt &component = *inserted;
    component.set(ID_from_base, true);
    component.set_access(new_access);

    // a member of a PACKED base keeps the base's packed layout in the
    // derived class (padding.cpp reads the mark; `struct P { char c; long
    // l; } __attribute__((packed)); struct D : P { int m; }' has m at 12)
    if(from.get_bool(ID_C_packed))
      component.set(ID_C_packed, true);

    // A padding component of the base's layout is named by its index in
    // the base (`$pad2'); two bases contribute clashing names, and the
    // derived class's own padding may want the same index.  Component
    // names must be unique within a struct type.
    if(component.get_is_padding())
    {
      component.set_name(
        id2string(component.get_name()) + "$b" +
        std::to_string(dest_c.size() - 1));
    }

    // put into scope
  }
}

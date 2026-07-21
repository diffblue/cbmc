/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/c_types.h>

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
        for(auto &sub : name.get_sub())
        {
          if(sub.id() == ID_template_args)
          {
            irept::subt &args = sub.add(ID_arguments).get_sub();
            for(auto &arg : args)
              template_map.apply(static_cast<exprt &>(arg));
          }
        }
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
      if(instantiation_stack.empty())
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

    const struct_typet &base_struct_type=
      to_struct_type(base_symbol.type);

    add_base_components(
      base_struct_type,
      class_access,
      type,
      bases,
      vbases,
      virtual_base);
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
    add_base_components(
      to_struct_type(symb.type),
      sub_access,
      to,
      bases,
      vbases,
      is_virtual_base);
  }

  // add the components
  struct_typet::componentst &dest_c=to.components();

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

  for(const auto &c : from.components())
  {
    const irep_idt new_access = inherited_access(access, c.get_access());

    if(c.get_bool(ID_from_base))
    {
      // The member is already flattened into `to` from its declaring
      // class via the recursion above.  Propagate its access as seen in
      // the immediate base `from` instead of keeping the declaring
      // class's access: an intermediate base may have changed it with a
      // using-declaration ([namespace.udecl]/19), e.g. binary_exprt's
      // public `using exprt::op0;` republishing the protected op0.
      for(auto &d : dest_c)
      {
        if(d.get_bool(ID_from_base) && d.get_name() == c.get_name())
          d.set_access(new_access);
      }
      continue;
    }

    // copy the component
    dest_c.push_back(c);

    // now twiddle the copy
    struct_typet::componentt &component=dest_c.back();
    component.set(ID_from_base, true);
    component.set_access(new_access);

    // put into scope
  }
}

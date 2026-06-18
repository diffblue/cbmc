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

#include <ostream>
#include <set>

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
        for(const auto &pt : *pack)
        {
          irept expanded = parameter;
          static_cast<typet &>(expanded.add(ID_type)) = pt;
          // The element type already carries the full (merged)
          // reference/pointer part; drop any declarator type and the
          // ellipsis flag so the element is not mis-elaborated.
          for(auto &d : expanded.get_sub())
            if(d.id() == ID_cpp_declarator)
            {
              static_cast<typet &>(d.add(ID_type)).make_nil();
              d.remove(ID_ellipsis);
            }
          new_parameters.push_back(expanded);
        }
        continue;
      }
    }
    new_parameters.push_back(parameter);
  }
  parameters.swap(new_parameters);
}

void template_mapt::apply(typet &type) const
{
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
    apply(to_pointer_type(type).base_type());
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
          for(auto &sub : decl_type.get_sub())
            apply(static_cast<typet &>(sub));
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
        auto matches_empty_pack = [this](irep_idt ident) -> bool
        {
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
              }
              for(const auto &c : n.get_named_sub())
                collect(c.second);
              for(const auto &c : n.get_sub())
                collect(c);
            };
            collect(static_cast<const exprt &>(arg).type());

            if(!referenced_packs.empty())
            {
              // All packs in a single expansion expand in lock-step and
              // therefore must have the same length ([temp.variadic]/5).
              const std::size_t n =
                pack_args_map.at(*referenced_packs.begin()).size();
              bool consistent = true;
              for(const auto &pid : referenced_packs)
                if(pack_args_map.at(pid).size() != n)
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
                    element_map.type_map[pid] = pack_args_map.at(pid)[i];
                    element_map.pack_args_map.erase(pid);
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
      for(auto &arg : args.get_sub())
      {
        if(arg.id() != ID_ambiguous)
          continue;
        // The ambiguous node stores the cpp_name in its "type" field
        const irept &inner = arg.find(ID_type);
        if(inner.id() != ID_cpp_name)
          continue;
        // Check if the cpp_name is a single identifier
        if(inner.get_sub().size() != 1 || inner.get_sub()[0].id() != ID_name)
          continue;
        const std::string target =
          id2string(inner.get_sub()[0].get(ID_identifier));
        for(const auto &entry : expr_map)
        {
          const std::string &key = id2string(entry.first);
          if(
            key == target ||
            (key.size() > target.size() + 2 &&
             key.substr(key.size() - target.size()) == target &&
             key[key.size() - target.size() - 1] == ':'))
          {
            arg = entry.second;
            break;
          }
        }
      }
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

exprt template_mapt::lookup_by_suffix(const std::string &suffix) const
{
  const std::string match = "::" + suffix;
  for(const auto &entry : type_map)
  {
    const std::string key = id2string(entry.first);
    if(
      key.size() >= match.size() &&
      key.compare(key.size() - match.size(), match.size(), match) == 0)
    {
      exprt e(ID_type);
      e.type() = entry.second;
      return e;
    }
  }
  for(const auto &entry : expr_map)
  {
    const std::string key = id2string(entry.first);
    if(
      key.size() >= match.size() &&
      key.compare(key.size() - match.size(), match.size(), match) == 0)
    {
      return entry.second;
    }
  }
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

  // these should have been typechecked before
  bool has_pack = !template_parameters.empty() &&
                  template_parameters.back().get_bool(ID_ellipsis);
  if(
    instance.size() != template_parameters.size() &&
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
  }

  std::size_t i = 0;
  for(cpp_template_args_tct::argumentst::const_iterator i_it = instance.begin();
      i_it != instance.end();
      i_it++, i++)
  {
    if(i < template_parameters.size())
    {
      // A *type* parameter pack must not be scalar-bound to its first
      // argument here: doing so records type_map[Pack] = <first element>,
      // which then collapses pack expansions and `sizeof...(Pack)` to a single
      // element.  Type packs are bound below via pack_args_map / pack_size_map
      // (and, for a single-element pack, a type_map convenience entry) per
      // [temp.variadic]/5,8.  Non-type packs are left to the existing scalar
      // binding (the pack block records only type elements).
      const bool is_type_pack = template_parameters[i].id() == ID_type &&
                                template_parameters[i].get_bool(ID_ellipsis);
      if(!is_type_pack)
        set(template_parameters[i], *i_it);
    }
    // Extra arguments for variadic packs are not mapped to individual
    // parameters; they are passed through in the template args.
  }

  // Record pack sizes for sizeof...(Pack)
  if(has_pack)
  {
    const auto &pack_param = template_parameters.back();
    irep_idt pack_id = pack_param.id() == ID_type
                         ? pack_param.type().get(ID_identifier)
                         : pack_param.get(ID_identifier);
    std::size_t non_pack = template_parameters.size() - 1;
    std::size_t pack_sz =
      instance.size() >= non_pack ? instance.size() - non_pack : 0;

    // Store all pack argument types for pack indexing (C++26)
    std::vector<typet> pack_types;
    for(std::size_t j = non_pack; j < instance.size(); ++j)
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
    pack_size_map[pack_id] = pack_sz;
    if(!pack_types.empty())
    {
      pack_args_map[pack_id] = std::move(pack_types);
      // Per [temp.variadic]/7: for single-element packs, also add
      // the type to type_map so template_map.apply() can substitute.
      if(pack_args_map[pack_id].size() == 1)
        type_map[pack_id] = pack_args_map[pack_id].front();
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

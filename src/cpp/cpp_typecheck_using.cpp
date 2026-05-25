/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/c_types.h>
#include <util/source_location.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

void cpp_typecheckt::convert(cpp_usingt &cpp_using)
{
  // there are two forms of using clauses:
  // a) using namespace SCOPE;  ("using directive")
  // b) using SCOPE::id;        ("using declaration")

  cpp_typecheck_resolvet resolver(*this);
  cpp_save_scopet save_scope(this->cpp_scopes);

  irep_idt base_name;
  cpp_template_args_non_tct template_args;
  resolver.resolve_scope(cpp_using.name(), base_name, template_args);

  // For "using _Mybase::_Mybase" where _Mybase is a typedef for Base,
  // resolve_scope navigates to Base's scope, but base_name is still
  // "_Mybase". Replace with the actual class name so constructor
  // lookup succeeds (inheriting constructors).
  {
    const irep_idt &current_scope_id = cpp_scopes.current_scope().identifier;
    const symbolt *scope_sym = symbol_table.lookup(current_scope_id);
    if(
      scope_sym != nullptr && scope_sym->is_type &&
      scope_sym->type.id() == ID_struct)
    {
      irep_idt class_base_name = scope_sym->base_name;
      if(base_name != class_base_name)
      {
        // Check if base_name is a typedef in the CALLING scope
        // that resolves to this class
        // If so, replace base_name with the class's base_name
        // (for inheriting constructor: using Typedef::Typedef -> Base::Base)
        auto check_set =
          cpp_scopes.current_scope().lookup(base_name, cpp_scopet::RECURSIVE);
        if(check_set.empty())
          base_name = class_base_name;
      }
    }
  }

  bool qualified=cpp_using.name().is_qualified();

  auto id_set = cpp_scopes.current_scope().lookup(
    base_name, qualified ? cpp_scopet::QUALIFIED : cpp_scopet::RECURSIVE);

  // Per [namespace.udecl]/3 (C++11+): a using-declaration of the
  // form `using Base::name;` must find `name` either in `Base` OR
  // in any (transitively) inherited class of `Base`.  Our QUALIFIED
  // scope lookup only searches within the immediate class scope, so
  // fall back to walking up the base-class list of `Base` when the
  // initial lookup returns nothing.
  if(id_set.empty() && qualified)
  {
    std::set<irep_idt> visited;
    std::vector<irep_idt> todo;
    const irep_idt &scope_id = cpp_scopes.current_scope().identifier;
    todo.push_back(scope_id);
    while(!todo.empty() && id_set.empty())
    {
      irep_idt cur = todo.back();
      todo.pop_back();
      if(!visited.insert(cur).second)
        continue;
      const symbolt *sym = symbol_table.lookup(cur);
      if(sym == nullptr)
        continue;
      const irept &bases = sym->type.find(ID_bases);
      for(const auto &b : bases.get_sub())
      {
        const typet &bt = static_cast<const typet &>(b.find(ID_type));
        if(bt.id() != ID_struct_tag)
          continue;
        const irep_idt &bid = to_struct_tag_type(bt).get_identifier();
        auto it = cpp_scopes.id_map.find(bid);
        if(it != cpp_scopes.id_map.end())
        {
          auto sub = static_cast<cpp_scopet &>(*it->second)
                       .lookup(base_name, cpp_scopet::SCOPE_ONLY);
          for(const auto *s : sub)
            id_set.insert(const_cast<cpp_idt *>(s));
        }
        todo.push_back(bid);
      }
    }
  }

  // Pragmatic fallback: if the lookup of a qualified using-
  // declaration still fails but the qualifier names a registered
  // type (i.e., we reached a struct scope via `Base::`), silently
  // drop the using-declaration.  CBMC does not model C++ access
  // control precisely, and a using-declaration that only adjusts
  // access (e.g. `using Base::private_member;` to republish a
  // protected member in the derived class) has no observable
  // effect on goto-conversion.  Erroring here would gate a large
  // class of header-only idioms (CBMC's own src/util/expr.h uses
  // this pattern with `using exprt::remove;`).
  if(id_set.empty() && qualified)
  {
    const symbolt *scope_sym =
      symbol_table.lookup(cpp_scopes.current_scope().identifier);
    if(
      scope_sym != nullptr && scope_sym->is_type &&
      (scope_sym->type.id() == ID_struct || scope_sym->type.id() == ID_union))
    {
      return;
    }
  }

  bool using_directive=cpp_using.get_namespace();

  if(id_set.empty())
  {
    // In system headers (e.g., libc++ <cstdlib>), using declarations may
    // reference identifiers not available on all platforms (e.g.,
    // at_quick_exit on macOS). Silently skip rather than fail.
    const auto &loc = cpp_using.name().source_location();
    const std::string file = id2string(loc.get_file());
    if(
      file.find("/usr/include/") == 0 || file.find("/usr/lib/") == 0 ||
      file.find("/Applications/") == 0)
    {
      return;
    }
    error().source_location = loc;
    error() << "using " << (using_directive ? "namespace" : "identifier")
            << " '" << base_name << "' not found" << eom;
    throw 0;
  }

  // go back to where we used to be
  save_scope.restore();

  for(cpp_scopest::id_sett::iterator
      it=id_set.begin();
      it!=id_set.end();
      it++)
  {
    if(using_directive)
    {
      if((*it)->id_class==cpp_idt::id_classt::NAMESPACE)
        cpp_scopes.current_scope().add_using_scope(
          static_cast<cpp_scopet &>(**it));
      else
      {
        // we should likely complain about this
      }
    }
    else // declaration
    {
      // we copy all 'normal' identifiers into the current scope
      if((*it)->id_class!=cpp_idt::id_classt::TEMPLATE_PARAMETER &&
         (*it)->id_class!=cpp_idt::id_classt::NAMESPACE)
      {
        cpp_scopes.current_scope().insert(**it);

        // C++20 using enum: import enumerators into scope
        const irep_idt &sym_id = (*it)->identifier;
        const symbolt *sym = symbol_table.lookup(sym_id);
        if(sym != nullptr)
        {
          const typet *enum_type = nullptr;
          if(sym->type.id() == ID_c_enum)
            enum_type = &sym->type;
          else if(sym->type.id() == ID_c_enum_tag)
          {
            const symbolt *tag_sym = symbol_table.lookup(
              to_c_enum_tag_type(sym->type).get_identifier());
            if(tag_sym != nullptr && tag_sym->type.id() == ID_c_enum)
              enum_type = &tag_sym->type;
          }

          if(enum_type != nullptr)
          {
            const auto &body =
              static_cast<const exprt &>(enum_type->find(ID_body));
            for(const auto &member : body.operands())
            {
              const irep_idt &base = member.get(ID_name);
              const irep_idt member_id =
                id2string(sym_id) + "::" + id2string(base);
              const symbolt *member_sym = symbol_table.lookup(member_id);
              if(member_sym != nullptr)
              {
                cpp_idt &new_id = cpp_scopes.put_into_scope(*member_sym);
                new_id.id_class = cpp_idt::id_classt::SYMBOL;
              }
            }
          }
        }
      }
    }
  }
}

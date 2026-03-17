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

  bool qualified=cpp_using.name().is_qualified();

  const auto id_set = cpp_scopes.current_scope().lookup(
    base_name, qualified ? cpp_scopet::QUALIFIED : cpp_scopet::RECURSIVE);

  bool using_directive=cpp_using.get_namespace();

  if(id_set.empty())
  {
    error().source_location=cpp_using.name().source_location();
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

/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/source_location.h>

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
    error() << "using "
            << (using_directive?"namespace":"identifier")
            << " `"
            << base_name << "' not found" << eom;
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
        cpp_scopes.current_scope().insert(**it);
    }
  }
}

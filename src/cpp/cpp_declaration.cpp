/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_declaration.h"

#include <ostream>

void cpp_declarationt::output(std::ostream &out) const
{
  out << "is_template: " << is_template() << '\n';
  out << "storage: " << storage_spec().pretty() << '\n';
  out << "template_type: " << template_type().pretty() << '\n';
  out << "type: " << type().pretty() << '\n';

  out << "Declarators:" << '\n';

  for(const auto &it : declarators())
  {
    it.output(out);
    out << '\n';
  }
}

void cpp_declarationt::name_anon_struct_union(typet &dest)
{
  // We name any anon struct/unions according to the first
  // declarator. No need to do anon enums, which get
  // a name based on the enum elements.

  if(dest.id()==ID_struct || dest.id()==ID_union)
  {
    if(dest.find(ID_tag).is_nil())
    {
      // it's anonymous

      const declaratorst &d=declarators();

      if(!d.empty() &&
         d.front().name().is_simple_name())
      {
        // Anon struct/unions without declarator are pretty
        // useless, but still possible.

        irep_idt base_name="anon-"+id2string(d.front().name().get_base_name());
        dest.set(ID_tag, cpp_namet(base_name));
        dest.set(ID_C_is_anonymous, true);
      }
    }
  }
  else if(dest.id()==ID_merged_type)
  {
    Forall_subtypes(it, dest)
      name_anon_struct_union(*it);
  }
}

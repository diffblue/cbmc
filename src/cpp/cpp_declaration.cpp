/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "cpp_declaration.h"

/*******************************************************************\

Function: cpp_declarationt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarationt::output(std::ostream &out) const
{
  out << "is_template: " << is_template() << std::endl;
  out << "storage: " << storage_spec().pretty() << std::endl;
  out << "template_type: " << template_type().pretty() << std::endl;
  out << "type: " << type().pretty() << std::endl;

  out << "Declarators:" << std::endl;

  forall_cpp_declarators(it, *this)
  {
    it->output(out);
    out << std::endl;
  }
}

/*******************************************************************\

Function: cpp_declarationt::name_anon_struct_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarationt::name_anon_struct_union()
{
  // We name any anon struct/unions according to the first
  // declarator. No need to do anon enums, which get
  // a name based on the enum elements.

  typet &dest=type();
  
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
        
        irep_idt base_name="anontag-"+id2string(d.front().name().get_base_name());
        dest.set(ID_tag, cpp_namet(base_name));
        dest.set(ID_C_is_anonymous, true);
      }
    }
  }
}

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

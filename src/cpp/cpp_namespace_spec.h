/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_NAMESPACE_SPEC_H
#define CPROVER_CPP_NAMESPACE_SPEC_H

#include <expr.h>

class cpp_namespace_spect:public exprt
{
public:
  cpp_namespace_spect():exprt(ID_cpp_namespace_spec)
  {
  }
  
  typedef std::vector<class cpp_itemt> itemst;

  const itemst &items() const
  {
    return (const itemst &)operands();
  }

  itemst &items()
  {
    return (itemst &)operands();
  }
  
  const irep_idt &get_namespace() const
  {
    return get(ID_namespace);
  }

  void set_namespace(const irep_idt &_namespace)
  {
    set(ID_namespace, _namespace);
  }
  
  irept &alias()
  {
    return add("alias");
  }
  
  const irept &alias() const
  {
    return find("alias");
  }
  
  void output(std::ostream &out) const;
};

#endif

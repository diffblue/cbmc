/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_NAMESPACE_SPEC_H
#define CPROVER_CPP_NAMESPACE_SPEC_H

#include <expr.h>

#include "cpp_name.h"

class cpp_namespace_spect:public exprt
{
public:
  inline cpp_namespace_spect():exprt(ID_cpp_namespace_spec)
  {
    add("alias").make_nil();
  }
  
  typedef std::vector<class cpp_itemt> itemst;

  inline const itemst &items() const
  {
    return (const itemst &)operands();
  }

  inline itemst &items()
  {
    return (itemst &)operands();
  }
  
  inline const irep_idt &get_namespace() const
  {
    return get(ID_namespace);
  }

  inline void set_namespace(const irep_idt &_namespace)
  {
    set(ID_namespace, _namespace);
  }
  
  inline cpp_namet &alias()
  {
    return static_cast<cpp_namet &>(add("alias"));
  }
  
  inline const cpp_namet &alias() const
  {
    return static_cast<const cpp_namet &>(find("alias"));
  }
  
  void output(std::ostream &out) const;
  
  inline void set_is_inline(bool value)
  {
    set(ID_is_inline, value);
  }

  inline bool get_is_inline() const
  {
    return get_bool(ID_is_inline);
  }
};

#endif

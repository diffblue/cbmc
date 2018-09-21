/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_NAMESPACE_SPEC_H
#define CPROVER_CPP_CPP_NAMESPACE_SPEC_H

#include <util/expr.h>

#include "cpp_name.h"

class cpp_namespace_spect:public exprt
{
public:
  cpp_namespace_spect():exprt(ID_cpp_namespace_spec)
  {
    alias().make_nil();
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

  cpp_namet &alias()
  {
    return static_cast<cpp_namet &>(add(ID_alias));
  }

  const cpp_namet &alias() const
  {
    return static_cast<const cpp_namet &>(find(ID_alias));
  }

  void output(std::ostream &out) const;

  void set_is_inline(bool value)
  {
    set(ID_is_inline, value);
  }

  bool get_is_inline() const
  {
    return get_bool(ID_is_inline);
  }
};

#endif // CPROVER_CPP_CPP_NAMESPACE_SPEC_H

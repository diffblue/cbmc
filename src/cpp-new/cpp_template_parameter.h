/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TEMPLATE_TYPE_H
#define CPROVER_CPP_TEMPLATE_TYPE_H

#include <util/type.h>

// A data structure for expressions of the form
// <typename T, int x, ...>
// Not to be confused with template arguments!

struct cpp_template_parametert:public irept
{
public:
  cpp_template_parametert():irept(ID_template_parameter)
  {
  }
  
  bool get_is_type() const
  {
    return get_bool(ID_is_type);
  }

  void set_is_type(bool value)
  {
    set(ID_is_type, value);
  }
  
  irep_idt get_identifier() const
  {
    return get(ID_identifier);
  }
  
  void set_identifier(const irep_idt &identifier)
  {
    return set(ID_identifier, identifier);
  }

  // the type of expression parameters
  typet &type()
  {
    return static_cast<typet &>(add(ID_type));
  }

  const typet &type() const
  {
    return static_cast<const typet &>(find(ID_type));
  }
};

#endif

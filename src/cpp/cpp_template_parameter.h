/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_CPP_CPP_TEMPLATE_PARAMETER_H
#define CPROVER_CPP_CPP_TEMPLATE_PARAMETER_H

#include <util/expr.h>

// A data structure for expressions of the form
// <typename T, int x, ...>
// Not to be confused with template arguments!

struct template_parametert:public exprt
{
public:
  template_parametert():exprt(ID_template_parameter)
  {
  }

  #if 0
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
  #endif

  exprt &default_argument()
  {
    return static_cast<exprt &>(add(ID_C_default_value));
  }

  const exprt &default_argument() const
  {
    return static_cast<const exprt &>(find(ID_C_default_value));
  }

  bool has_default_argument() const
  {
    return find(ID_C_default_value).is_not_nil();
  }
};

#endif // CPROVER_CPP_CPP_TEMPLATE_PARAMETER_H

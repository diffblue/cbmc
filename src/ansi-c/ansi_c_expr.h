/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_EXPR_H
#define CPROVER_ANSI_C_EXPR_H

#include <expr.h>

class string_constantt:public exprt
{
public:
  string_constantt();

  friend inline const string_constantt &to_string_constant(const exprt &expr)
  {
    assert(expr.id()==ID_string_constant);
    return static_cast<const string_constantt &>(expr);
  }

  friend inline string_constantt &to_string_constant(exprt &expr)
  {
    assert(expr.id()==ID_string_constant);
    return static_cast<string_constantt &>(expr);
  }
  
  void set_value(const irep_idt &value);

  inline const irep_idt &get_value() const
  {
    return get(ID_value);
  }
  
  void set_long(bool _long);

  inline bool get_long() const
  {
    return get_bool(ID_long);
  }
};

const string_constantt &to_string_constant(const exprt &expr);
string_constantt &to_string_constant(exprt &expr);

#endif

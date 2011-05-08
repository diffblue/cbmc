/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>

#include "ansi_c_expr.h"
#include "c_types.h"

/*******************************************************************\

Function: string_constantt::set_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

string_constantt::string_constantt():
  exprt(ID_string_constant)
{
  set_value(irep_idt());
  type()=typet(ID_array);
  type().subtype()=char_type();
}

/*******************************************************************\

Function: string_constantt::set_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_constantt::set_value(const irep_idt &value)
{
  exprt size_expr=from_integer(value.size()+1, int_type());
  type().add(ID_size).swap(size_expr);
  set(ID_value, value);
}

/*******************************************************************\

Function: string_constantt::set_long

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_constantt::set_long(bool is_long)
{
  set(ID_long, is_long);
  type().subtype()=is_long?wchar_t_type():char_type();
}

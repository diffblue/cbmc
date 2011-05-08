/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "type.h"

/*******************************************************************\

Function: typet::copy_to_subtypes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void typet::copy_to_subtypes(const typet &type)
{
  subtypes().push_back(type);
}

/*******************************************************************\

Function: typet::move_to_subtypes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void typet::move_to_subtypes(typet &type)
{
  subtypest &sub=subtypes();
  sub.push_back(static_cast<const typet &>(get_nil_irep()));
  sub.back().swap(type);
}

/*******************************************************************\

Function: is_number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_number(const typet &type)
{
  const irep_idt &id=type.id();
  return id==ID_rational ||
         id==ID_real ||
         id==ID_integer ||
         id==ID_natural || 
         id==ID_complex ||
         id==ID_unsignedbv ||
         id==ID_signedbv || 
         id==ID_floatbv ||
         id==ID_fixedbv;
}

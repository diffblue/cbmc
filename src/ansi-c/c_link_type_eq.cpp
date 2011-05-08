/*******************************************************************\

Module: Link Type Comparison

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <base_type.h>

/*******************************************************************\

   Class: c_link_type_eqt

 Purpose:

\*******************************************************************/

class c_link_type_eqt:public base_type_eqt
{
public:
  c_link_type_eqt(const namespacet &_ns):base_type_eqt(_ns)
  {
  }

protected:
  bool base_type_eq_rec(const typet &type1, const typet &type2);
};

/*******************************************************************\

Function: c_link_type_eqt::c_link_type_eq_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool c_link_type_eqt::base_type_eq_rec(
  const typet &type1,
  const typet &type2)
{
  // we are more generous than base_type_eq
  
  if(type1.id()==ID_struct &&
     type2.id()==ID_incomplete_struct)
    return true;

  if(type1.id()==ID_incomplete_struct &&
     type2.id()==ID_struct)
    return true;

  return base_type_eqt::base_type_eq_rec(type1, type2);
}

/*******************************************************************\

Function: c_link_type_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool c_link_type_eq(
  const typet &type1,
  const typet &type2,
  const namespacet &ns)
{
  c_link_type_eqt c_link_type_eq(ns);
  return c_link_type_eq.base_type_eq(type1, type2);
}

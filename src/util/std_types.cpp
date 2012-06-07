/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>

#include "arith_tools.h"
#include "std_types.h"
#include "std_expr.h"

/*******************************************************************\

Function: bitvector_typet::get_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned bitvector_typet::get_width() const
{
  return get_int(ID_width);
}

/*******************************************************************\

Function: fixedbv_typet::get_integer_bits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned fixedbv_typet::get_integer_bits() const
{
  const std::string &integer_bits=get_string("integer_bits");
  assert(integer_bits!="");
  return atoi(integer_bits.c_str());
}

/*******************************************************************\

Function: floatbv_typet::get_f

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned floatbv_typet::get_f() const
{
  const std::string &f=get_string(ID_f);
  assert(f!="");
  return atoi(f.c_str());
}

/*******************************************************************\

Function: struct_union_typet::component_number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned struct_union_typet::component_number(
  const irep_idt &component_name) const
{
  const componentst &c=components();

  unsigned number=0;

  for(componentst::const_iterator
      it=c.begin();
      it!=c.end();
      it++)
  {
    if(it->get_name()==component_name)
      return number;

    number++;
  }

  assert(false);
  return 0;
}

/*******************************************************************\

Function: struct_union_typet::get_component

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const struct_union_typet::componentt &struct_union_typet::get_component(
  const irep_idt &component_name) const
{
  const componentst &c=components();

  for(componentst::const_iterator
      it=c.begin();
      it!=c.end();
      it++)
  {
    if(it->get_name()==component_name)
      return *it;
  }

  return static_cast<const componentt &>(get_nil_irep());
}

/*******************************************************************\

Function: struct_union_typet::component_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet struct_union_typet::component_type(
  const irep_idt &component_name) const
{
  const exprt c=get_component(component_name);
  assert(c.is_not_nil());
  return c.type();
}

/*******************************************************************\

Function: struct_typet::is_prefix_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool struct_typet::is_prefix_of(const struct_typet &other) const
{
  const componentst &ot_components=other.components();
  const componentst &tt_components=components();

  if(ot_components.size()<
     tt_components.size())
    return false; 

  componentst::const_iterator
    ot_it=ot_components.begin();

  for(componentst::const_iterator tt_it=
      tt_components.begin();
      tt_it!=tt_components.end();
      tt_it++)
  {
    if(ot_it->type()!=tt_it->type() ||
       ot_it->get(ID_name)!=tt_it->get(ID_name))
    {
      return false; // they just don't match
    }

    ot_it++;
  }

  return true; // ok, *this is a prefix of ot
}

/*******************************************************************\

Function: is_reference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_reference(const typet &type)
{
  return type.id()==ID_pointer &&
         type.get_bool(ID_C_reference);
}

/*******************************************************************\

Function: is_rvalue_reference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_rvalue_reference(const typet &type)
{
  return type.id()==ID_pointer &&
         type.get_bool(ID_C_rvalue_reference);
}

/*******************************************************************\

Function: range_typet::set_from

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void range_typet::set_from(const mp_integer &from)
{
  set(ID_from, integer2string(from));
}

/*******************************************************************\

Function: range_typet::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void range_typet::set_to(const mp_integer &to)
{
  set(ID_to, integer2string(to));
}

/*******************************************************************\

Function: range_typet::get_from

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer range_typet::get_from() const
{
  return string2integer(get_string(ID_from));
}

/*******************************************************************\

Function: range_typet::get_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer range_typet::get_to() const
{
  return string2integer(get_string(ID_to));
}

/*******************************************************************\

Function: signedbv_typet::smallest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer signedbv_typet::smallest() const
{
  return -power(2, get_width()-1);
}

/*******************************************************************\

Function: signedbv_typet::largest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer signedbv_typet::largest() const
{
  return power(2, get_width()-1)-1;
}

/*******************************************************************\

Function: signedbv_typet::smallest_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt signedbv_typet::smallest_expr() const
{
  return to_constant_expr(from_integer(smallest(), *this));
}

/*******************************************************************\

Function: signedbv_typet::largest_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt signedbv_typet::largest_expr() const
{
  return to_constant_expr(from_integer(largest(), *this));
}

/*******************************************************************\

Function: unsignedbv_typet::smallest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer unsignedbv_typet::smallest() const
{
  return 0;
}

/*******************************************************************\

Function: unsignedbv_typet::largest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer unsignedbv_typet::largest() const
{
  return power(2, get_width())-1;
}

/*******************************************************************\

Function: unsignedbv_typet::smallest_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt unsignedbv_typet::smallest_expr() const
{
  return to_constant_expr(from_integer(smallest(), *this));
}

/*******************************************************************\

Function: unsignedbv_typet::largest_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt unsignedbv_typet::largest_expr() const
{
  return to_constant_expr(from_integer(largest(), *this));
}

/*******************************************************************\

Function: c_bool_typet::smallest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer c_bool_typet::smallest() const
{
  return 0;
}

/*******************************************************************\

Function: c_bool_typet::largest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer c_bool_typet::largest() const
{
  return 1;
}

/*******************************************************************\

Function: c_bool_typet::constant_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt c_bool_typet::constant_false() const
{
  return to_constant_expr(from_integer(0, *this));
}

/*******************************************************************\

Function: c_bool_typet::constant_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt c_bool_typet::constant_true() const
{
  return to_constant_expr(from_integer(1, *this));
}

/*******************************************************************\

Function: c_bool_typet::smallest_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt c_bool_typet::smallest_expr() const
{
  return to_constant_expr(from_integer(0, *this));
}

/*******************************************************************\

Function: c_bool_typet::largest_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt c_bool_typet::largest_expr() const
{
  return to_constant_expr(from_integer(1, *this));
}


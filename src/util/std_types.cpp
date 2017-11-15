/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_types.h"

#include "string2int.h"
#include "arith_tools.h"
#include "std_expr.h"

std::size_t fixedbv_typet::get_integer_bits() const
{
  const irep_idt integer_bits=get(ID_integer_bits);
  assert(!integer_bits.empty());
  return unsafe_string2unsigned(id2string(integer_bits));
}

std::size_t floatbv_typet::get_f() const
{
  const irep_idt &f=get(ID_f);
  assert(!f.empty());
  return unsafe_string2unsigned(id2string(f));
}

std::size_t struct_union_typet::component_number(
  const irep_idt &component_name) const
{
  const componentst &c=components();

  std::size_t number=0;

  for(componentst::const_iterator
      it=c.begin();
      it!=c.end();
      it++)
  {
    if(it->get_name()==component_name)
      return number;

    number++;
  }

  UNREACHABLE;
  return 0;
}

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

typet struct_union_typet::component_type(
  const irep_idt &component_name) const
{
  const exprt c=get_component(component_name);
  assert(c.is_not_nil());
  return c.type();
}

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

bool is_reference(const typet &type)
{
  return type.id()==ID_pointer &&
         type.get_bool(ID_C_reference);
}

bool is_rvalue_reference(const typet &type)
{
  return type.id()==ID_pointer &&
         type.get_bool(ID_C_rvalue_reference);
}

void range_typet::set_from(const mp_integer &from)
{
  set(ID_from, integer2string(from));
}

void range_typet::set_to(const mp_integer &to)
{
  set(ID_to, integer2string(to));
}

mp_integer range_typet::get_from() const
{
  return string2integer(get_string(ID_from));
}

mp_integer range_typet::get_to() const
{
  return string2integer(get_string(ID_to));
}

mp_integer signedbv_typet::smallest() const
{
  return -power(2, get_width()-1);
}

mp_integer signedbv_typet::largest() const
{
  return power(2, get_width()-1)-1;
}

constant_exprt signedbv_typet::zero_expr() const
{
  return from_integer(0, *this);
}

constant_exprt signedbv_typet::smallest_expr() const
{
  return from_integer(smallest(), *this);
}

constant_exprt signedbv_typet::largest_expr() const
{
  return from_integer(largest(), *this);
}

mp_integer unsignedbv_typet::smallest() const
{
  return 0;
}

mp_integer unsignedbv_typet::largest() const
{
  return power(2, get_width())-1;
}

constant_exprt unsignedbv_typet::zero_expr() const
{
  return from_integer(0, *this);
}

constant_exprt unsignedbv_typet::smallest_expr() const
{
  return from_integer(smallest(), *this);
}

constant_exprt unsignedbv_typet::largest_expr() const
{
  return from_integer(largest(), *this);
}

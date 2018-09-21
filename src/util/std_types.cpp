/*******************************************************************\

Module: Pre-defined types

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Pre-defined types

#include "std_types.h"

#include "arith_tools.h"
#include "namespace.h"
#include "std_expr.h"
#include "string2int.h"

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

/// Return the sequence number of the component with given name.
std::size_t struct_union_typet::component_number(
  const irep_idt &component_name) const
{
  std::size_t number=0;

  for(const auto &c : components())
  {
    if(c.get_name() == component_name)
      return number;

    number++;
  }

  UNREACHABLE;
  return 0;
}

/// Get the reference to a component with given name.
const struct_union_typet::componentt &struct_union_typet::get_component(
  const irep_idt &component_name) const
{
  for(const auto &c : components())
  {
    if(c.get_name() == component_name)
      return c;
  }

  return static_cast<const componentt &>(get_nil_irep());
}

const typet &
struct_union_typet::component_type(const irep_idt &component_name) const
{
  const auto &c = get_component(component_name);
  assert(c.is_not_nil());
  return c.type();
}

/// Returns true if the struct is a prefix of \a other, i.e., if this struct
/// has n components then the component types and names of this struct must
/// match the first n components of \a other struct.
/// \param other Struct type to compare with.
bool struct_typet::is_prefix_of(const struct_typet &other) const
{
  const componentst &ot_components=other.components();
  const componentst &tt_components=components();

  if(ot_components.size()<
     tt_components.size())
    return false;

  componentst::const_iterator
    ot_it=ot_components.begin();

  for(const auto &tt_c : tt_components)
  {
    if(ot_it->type() != tt_c.type() || ot_it->get_name() != tt_c.get_name())
    {
      return false; // they just don't match
    }

    ot_it++;
  }

  return true; // ok, *this is a prefix of ot
}

/// Returns true if the type is a reference.
bool is_reference(const typet &type)
{
  return type.id()==ID_pointer &&
         type.get_bool(ID_C_reference);
}

/// Returns if the type is an R value reference.
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

/// Identify whether a given type is constant itself or contains constant
/// components.
/// Examples include:
///  - const int a;
///  - struct contains_constant_pointer {  int x; int * const p; };
///  - const int b[3];
/// \param type The type we want to query constness of.
/// \param ns The namespace, needed for resolution of symbols.
/// \return Whether passed in type is const or not.
bool is_constant_or_has_constant_components(
  const typet &type,
  const namespacet &ns)
{
  // Helper function to avoid the code duplication in the branches
  // below.
  const auto has_constant_components = [&ns](const typet &subtype) -> bool {
    if(subtype.id() == ID_struct || subtype.id() == ID_union)
    {
      const auto &struct_union_type = to_struct_union_type(subtype);
      for(const auto &component : struct_union_type.components())
      {
        if(is_constant_or_has_constant_components(component.type(), ns))
          return true;
      }
    }
    return false;
  };

  // There are 4 possibilities the code below is handling.
  // The possibilities are enumerated as comments, to show
  // what each code is supposed to be handling. For more
  // comprehensive test case for this, take a look at
  // regression/cbmc/no_nondet_static/main.c

  // const int a;
  if(type.get_bool(ID_C_constant))
    return true;

  // This is a termination condition to break the recursion
  // for recursive types such as the following:
  // struct list { const int datum; struct list * next; };
  // NOTE: the difference between this condition and the previous
  // one is that this one always returns.
  if(type.id() == ID_pointer)
    return type.get_bool(ID_C_constant);

  // When we have a case like the following, we don't immediately
  // see the struct t. Instead, we only get to see symbol t1, which
  // we have to use the namespace to resolve to its definition:
  // struct t { const int a; };
  // struct t t1;
  if(type.id() == ID_symbol_type ||
     type.id() == ID_struct_tag ||
     type.id() == ID_union_tag)
  {
    const auto &resolved_type = ns.follow(type);
    return has_constant_components(resolved_type);
  }

  // In a case like this, where we see an array (b[3] here), we know that
  // the array contains subtypes. We get the first one, and
  // then resolve it to its  definition through the usage of the namespace.
  // struct contains_constant_pointer { int x; int * const p; };
  // struct contains_constant_pointer b[3] = { {23, &y}, {23, &y}, {23, &y} };
  if(type.has_subtype())
  {
    const auto &subtype = type.subtype();
    return is_constant_or_has_constant_components(subtype, ns);
  }

  return false;
}

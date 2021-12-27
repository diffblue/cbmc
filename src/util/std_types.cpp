/*******************************************************************\

Module: Pre-defined types

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Pre-defined types

#include "std_types.h"

#include "c_types.h"
#include "namespace.h"
#include "std_expr.h"

void array_typet::check(const typet &type, const validation_modet vm)
{
  PRECONDITION(type.id() == ID_array);
  const array_typet &array_type = static_cast<const array_typet &>(type);
  if(array_type.size().is_nil())
  {
    DATA_CHECK(
      vm,
      array_type.size() == nil_exprt{},
      "nil array size must be exactly nil");
  }
}

typet array_typet::index_type() const
{
  // we may wish to make the index type part of the array type
  return ::index_type();
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
  CHECK_RETURN(c.is_not_nil());
  return c.type();
}

struct_tag_typet &struct_typet::baset::type()
{
  return to_struct_tag_type(exprt::type());
}

const struct_tag_typet &struct_typet::baset::type() const
{
  return to_struct_tag_type(exprt::type());
}

struct_typet::baset::baset(struct_tag_typet base)
  : exprt(ID_base, std::move(base))
{
}

void struct_typet::add_base(const struct_tag_typet &base)
{
  bases().push_back(baset(base));
}

optionalt<struct_typet::baset> struct_typet::get_base(const irep_idt &id) const
{
  for(const auto &b : bases())
  {
    if(to_struct_tag_type(b.type()).get_identifier() == id)
      return b;
  }
  return {};
}

/// Returns true if the struct is a prefix of \a other, i.e., if this struct
/// has n components then the component types and names of this struct must
/// match the first n components of \a other struct.
/// \param other: Struct type to compare with.
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

/// Identify whether a given type is constant itself or contains constant
/// components.
/// Examples include:
///  - const int a;
///  - struct contains_constant_pointer {  int x; int * const p; };
///  - const int b[3];
/// \param type: The type we want to query constness of.
/// \param ns: The namespace, needed for resolution of symbols.
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
  if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
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
    const auto &subtype = to_type_with_subtype(type).subtype();
    return is_constant_or_has_constant_components(subtype, ns);
  }

  return false;
}

vector_typet::vector_typet(const typet &_subtype, const constant_exprt &_size)
  : type_with_subtypet(ID_vector, _subtype)
{
  size() = _size;
}

typet vector_typet::index_type() const
{
  // we may wish to make the index type part of the vector type
  return ::index_type();
}

const constant_exprt &vector_typet::size() const
{
  return static_cast<const constant_exprt &>(find(ID_size));
}

constant_exprt &vector_typet::size()
{
  return static_cast<constant_exprt &>(add(ID_size));
}

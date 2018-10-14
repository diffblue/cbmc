/*******************************************************************\

Module: Defines typet, type_with_subtypet and type_with_subtypest

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Defines typet, type_with_subtypet and type_with_subtypest

#ifndef CPROVER_UTIL_TYPE_H
#define CPROVER_UTIL_TYPE_H

#include "source_location.h"

/// The type of an expression, extends irept. Types may have subtypes. This is
/// modeled with two subs named “subtype” (a single type) and “subtypes”
/// (a vector of types). The class typet only adds specialized methods
/// for accessing the subtype information to the interface of irept.
/// For pre-defined types see `std_types.h` and `mathematical_types.h`.
class typet:public irept
{
public:
  typet() { }

  explicit typet(const irep_idt &_id):irept(_id) { }
  typet(const irep_idt &_id, const typet &_subtype):irept(_id)
  {
    subtype()=_subtype;
  }

  const typet &subtype() const
  {
    if(get_sub().empty())
      return static_cast<const typet &>(get_nil_irep());
    return static_cast<const typet &>(get_sub().front());
  }

  typet &subtype()
  {
    subt &sub=get_sub();
    if(sub.empty())
      sub.resize(1);
    return static_cast<typet &>(sub.front());
  }

  bool has_subtypes() const
  { return !get_sub().empty(); }

  bool has_subtype() const
  { return !get_sub().empty(); }

  void remove_subtype()
  { get_sub().clear(); }

  const source_locationt &source_location() const
  {
    return (const source_locationt &)find(ID_C_source_location);
  }

  source_locationt &add_source_location()
  {
    return static_cast<source_locationt &>(add(ID_C_source_location));
  }

  typet &add_type(const irep_namet &name)
  {
    return static_cast<typet &>(add(name));
  }

  const typet &find_type(const irep_namet &name) const
  {
    return static_cast<const typet &>(find(name));
  }
};

/// Type with a single subtype.
class type_with_subtypet:public typet
{
public:
  explicit type_with_subtypet(const irep_idt &_id):typet(_id) { }
  type_with_subtypet(const irep_idt &_id, const typet &_subtype):
    typet(_id)
  {
    subtype()=_subtype;
  }

  #if 0
  const typet &subtype() const
  { return (typet &)find(ID_subtype); }

  typet &subtype()
  { return (typet &)add(ID_subtype); }
  #endif
};

inline const type_with_subtypet &to_type_with_subtype(const typet &type)
{
  PRECONDITION(type.has_subtype());
  return static_cast<const type_with_subtypet &>(type);
}

inline type_with_subtypet &to_type_with_subtype(typet &type)
{
  PRECONDITION(type.has_subtype());
  return static_cast<type_with_subtypet &>(type);
}

/// Type with multiple subtypes.
class type_with_subtypest:public typet
{
public:
  typedef std::vector<typet> subtypest;

  type_with_subtypest() { }

  explicit type_with_subtypest(const irep_idt &_id):typet(_id) { }

  type_with_subtypest(const irep_idt &_id, const subtypest &_subtypes)
    : typet(_id)
  {
    subtypes() = _subtypes;
  }

  type_with_subtypest(const irep_idt &_id, subtypest &&_subtypes) : typet(_id)
  {
    subtypes() = std::move(_subtypes);
  }

  subtypest &subtypes()
  {
    return (subtypest &)get_sub();
  }

  const subtypest &subtypes() const
  {
    return (const subtypest &)get_sub();
  }

  void move_to_subtypes(typet &type); // destroys type

  void copy_to_subtypes(const typet &type);
};

inline const type_with_subtypest &to_type_with_subtypes(const typet &type)
{
  return static_cast<const type_with_subtypest &>(type);
}

inline type_with_subtypest &to_type_with_subtypes(typet &type)
{
  return static_cast<type_with_subtypest &>(type);
}

#define forall_subtypes(it, type) \
  if((type).has_subtypes()) /* NOLINT(readability/braces) */ \
    for(type_with_subtypest::subtypest::const_iterator it=to_type_with_subtypes(type).subtypes().begin(), \
        it##_end=to_type_with_subtypes(type).subtypes().end(); \
        it!=it##_end; ++it)

#define Forall_subtypes(it, type) \
  if((type).has_subtypes()) /* NOLINT(readability/braces) */ \
    for(type_with_subtypest::subtypest::iterator it=to_type_with_subtypes(type).subtypes().begin(); \
        it!=to_type_with_subtypes(type).subtypes().end(); ++it)

#endif // CPROVER_UTIL_TYPE_H

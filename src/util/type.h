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

#define SUBTYPE_IN_GETSUB
#define SUBTYPES_IN_GETSUB

/// The type of an expression, extends irept. Types may have subtypes. This is
/// modeled with two subs named “subtype” (a single type) and “subtypes”
/// (a vector of types). The class typet only adds specialized methods
/// for accessing the subtype information to the interface of irept.
/// For pre-defined types see `std_types.h`.
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
  #ifdef SUBTYPE_IN_GETSUB
  {
    if(get_sub().empty())
      return static_cast<const typet &>(get_nil_irep());
    return static_cast<const typet &>(get_sub().front());
  }
  #else
  { return (typet &)find(ID_subtype); }
  #endif

  typet &subtype()
  #ifdef SUBTYPE_IN_GETSUB
  {
    subt &sub=get_sub();
    if(sub.empty())
      sub.resize(1);
    return static_cast<typet &>(sub.front());
  }
  #else
  { return (typet &)add(ID_subtype); }
  #endif

  typedef std::vector<typet> subtypest;

  subtypest &subtypes()
  #ifdef SUBTYPES_IN_GETSUB
  { return (subtypest &)get_sub(); }
  #else
  { return (subtypest &)add(ID_subtypes).get_sub(); }
  #endif

  const subtypest &subtypes() const
  #ifdef SUBTYPES_IN_GETSUB
  { return (const subtypest &)get_sub(); }
  #else
  { return (const subtypest &)find(ID_subtypes).get_sub(); }
  #endif

  bool has_subtypes() const
  #ifdef SUBTYPES_IN_GETSUB
  { return !get_sub().empty(); }
  #else
  { return !find(ID_subtypes).is_nil(); }
  #endif

  bool has_subtype() const
  #ifdef SUBTYPE_IN_GETSUB
  { return !get_sub().empty(); }
  #else
  { return !find(ID_subtype).is_nil(); }
  #endif

  void remove_subtype()
  #ifdef SUBTYPE_IN_GETSUB
  { get_sub().clear(); }
  #else
  { remove(ID_subtype); }
  #endif

  void move_to_subtypes(typet &type);

  void copy_to_subtypes(const typet &type);

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
  type_with_subtypet() { }

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

/// Type with multiple subtypes.
class type_with_subtypest:public typet
{
public:
  type_with_subtypest() { }

  explicit type_with_subtypest(const irep_idt &_id):typet(_id) { }

  #if 0
  typedef std::vector<typet> subtypest;

  subtypest &subtypes()
  { return (subtypest &)add(ID_subtypes).get_sub(); }

  const subtypest &subtypes() const
  { return (const subtypest &)find(ID_subtypes).get_sub(); }

  void move_to_subtypes(typet &type); // destroys expr

  void copy_to_subtypes(const typet &type);
  #endif
};

#define forall_subtypes(it, type) \
  if((type).has_subtypes()) /* NOLINT(readability/braces) */ \
    for(typet::subtypest::const_iterator it=(type).subtypes().begin(), \
        it##_end=(type).subtypes().end(); \
        it!=it##_end; ++it)

#define Forall_subtypes(it, type) \
  if((type).has_subtypes()) /* NOLINT(readability/braces) */ \
    for(typet::subtypest::iterator it=(type).subtypes().begin(); \
        it!=(type).subtypes().end(); ++it)

#endif // CPROVER_UTIL_TYPE_H

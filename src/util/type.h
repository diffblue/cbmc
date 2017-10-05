/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_TYPE_H
#define CPROVER_UTIL_TYPE_H

#include <util/source_location.h>

#define SUBTYPE_IN_GETSUB
#define SUBTYPES_IN_GETSUB

/*! \brief The type of an expression
*/
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

  using subtypest = std::vector<typet>;

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

  void move_to_subtypes(typet &type); // destroys expr

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

class type_with_subtypest:public typet
{
public:
  type_with_subtypest() { }

  explicit type_with_subtypest(const irep_idt &_id):typet(_id) { }

  #if 0
  using subtypest = std::vector<typet>;

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

/*

pre-defined types:
  universe      // super type
  type          // another type
  predicate     // predicate expression (subtype and predicate)
  uninterpreted // uninterpreted type with identifier
  empty         // void
  bool          // true or false
  abstract      // abstract super type
  struct        // with components: each component has name and type
                // the ordering matters
  rational
  real
  integer
  complex
  string
  enum          // with elements
                // the ordering does not matter
  tuple         // with components: each component has type
                // the ordering matters
  mapping       // domain -> range
  bv            // no interpretation
  unsignedbv
  signedbv      // two's complement
  floatbv       // IEEE floating point format
  code
  pointer       // for ANSI-C (subtype)
  symbol        // look in symbol table (identifier)
  number        // generic number super type

*/

bool is_number(const typet &type);
// rational, real, integer, complex, unsignedbv, signedbv, floatbv

#endif // CPROVER_UTIL_TYPE_H

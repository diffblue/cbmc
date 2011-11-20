/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TYPE_H
#define CPROVER_TYPE_H

#include <list>

#include <location.h>

/*! \brief The type of an expression
*/
class typet:public irept
{
public:
  typet() { }
   
  explicit typet(const irep_idt &_id):irept(_id) { }
  
  const typet &subtype() const
  { return (typet &)find(ID_subtype); }
   
  typet &subtype()
  { return (typet &)add(ID_subtype); }
   
  typedef std::vector<typet> subtypest;

  subtypest &subtypes()
  { return (subtypest &)add(ID_subtypes).get_sub(); }
  
  const subtypest &subtypes() const
  { return (const subtypest &)find(ID_subtypes).get_sub(); }
   
  bool has_subtypes() const
  { return !find(ID_subtypes).is_nil(); }
   
  bool has_subtype() const
  { return !find(ID_subtype).is_nil(); }

  void move_to_subtypes(typet &type); // destroys expr

  void copy_to_subtypes(const typet &type);

  const locationt &location() const
  {
    return (const locationt &)find(ID_C_location);
  }

  locationt &location()
  {
    return (locationt &)add(ID_C_location);
  }
  
  typet &add_type(const irep_namet &name)
  {
    return (typet &)add(name);
  }

  const typet &find_type(const irep_namet &name) const
  {
    return (const typet &)find(name);
  }
};

typedef std::list<typet> type_listt;

#define forall_type_list(it, type) \
  for(type_listt::const_iterator it=(type).begin(); \
      it!=(type).end(); it++)

#define Forall_type_list(it, type) \
  for(type_listt::iterator it=(type).begin(); \
      it!=(type).end(); it++)

#define forall_subtypes(it, type) \
  if((type).has_subtypes()) \
    for(typet::subtypest::const_iterator it=(type).subtypes().begin(); \
        it!=(type).subtypes().end(); it++)

#define Forall_subtypes(it, type) \
  if((type).has_subtypes()) \
    for(typet::subtypest::iterator it=(type).subtypes().begin(); \
        it!=(type).subtypes().end(); it++)

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

#endif

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_IREP_H
#define CPROVER_UTIL_IREP_H

#include <vector>
#include <string>
#include <cassert>
#include <iosfwd>

#include "irep_ids.h"

#define SHARING
// #define HASH_CODE
// #define SUB_IS_LIST

#ifdef SHARING
#include "small_shared_ptr.h"
#endif

#ifdef SUB_IS_LIST
#include <list>
#else
#include <map>
#endif

#ifdef USE_DSTRING
typedef dstringt irep_idt;
typedef dstringt irep_namet;
// NOLINTNEXTLINE(readability/identifiers)
typedef dstring_hash irep_id_hash;
#else
#include "string_hash.h"
typedef std::string irep_idt;
typedef std::string irep_namet;
// NOLINTNEXTLINE(readability/identifiers)
typedef string_hash irep_id_hash;
#endif

inline const std::string &id2string(const irep_idt &d)
{
  #ifdef USE_DSTRING
  return as_string(d);
  #else
  return d;
  #endif
}

inline const std::string &name2string(const irep_namet &n)
{
  #ifdef USE_DSTRING
  return as_string(n);
  #else
  return n;
  #endif
}

#define forall_irep(it, irep) \
  for(irept::subt::const_iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#define Forall_irep(it, irep) \
  for(irept::subt::iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#define forall_named_irep(it, irep) \
  for(irept::named_subt::const_iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#define Forall_named_irep(it, irep) \
  for(irept::named_subt::iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#ifdef IREP_DEBUG
#include <iostream>
#endif

class irept;
const irept &get_nil_irep();

/*! \brief Base class for tree-like data structures with sharing
*/
class irept
{
public:
  // These are not stable.
  typedef std::vector<irept> subt;

  // named_subt has to provide stable references; with C++11 we could
  // use std::forward_list or std::vector< unique_ptr<T> > to save
  // memory and increase efficiency.

  #ifdef SUB_IS_LIST
  typedef std::list<std::pair<irep_namet, irept> > named_subt;
  #else
  typedef std::map<irep_namet, irept> named_subt;
  #endif

  bool is_nil() const { return id()==ID_nil; }
  bool is_not_nil() const { return id()!=ID_nil; }

  irept()=default;

  explicit irept(const irep_idt &_id)
  {
    id(_id);
  }

  const irep_idt &id() const
  { return read().data; }

  const std::string &id_string() const
  { return id2string(read().data); }

  void id(const irep_idt &_data)
  { write().data=_data; }

  const irept &find(const irep_namet &name) const;
  irept &add(const irep_namet &name);
  irept &add(const irep_namet &name, const irept &irep);

  const std::string &get_string(const irep_namet &name) const
  {
    return id2string(get(name));
  }

  const irep_idt &get(const irep_namet &name) const;
  bool get_bool(const irep_namet &name) const;
  signed int get_int(const irep_namet &name) const;
  unsigned int get_unsigned_int(const irep_namet &name) const;
  std::size_t get_size_t(const irep_namet &name) const;
  long long get_long_long(const irep_namet &name) const;

  void set(const irep_namet &name, const irep_idt &value)
  { add(name).id(value); }
  void set(const irep_namet &name, const irept &irep)
  { add(name, irep); }
  void set(const irep_namet &name, const long long value);

  void remove(const irep_namet &name);
  void move_to_sub(irept &irep);
  void move_to_named_sub(const irep_namet &name, irept &irep);

  bool operator==(const irept &other) const;

  bool operator!=(const irept &other) const
  {
    return !(*this==other);
  }

  void swap(irept &irep)
  {
    std::swap(irep.data, data);
  }

  bool operator<(const irept &other) const;
  bool ordering(const irept &other) const;

  int compare(const irept &i) const;

  void clear() { *this=irept(); }

  void make_nil() { *this=get_nil_irep(); }

  subt &get_sub() { return write().sub; } // DANGEROUS
  const subt &get_sub() const { return read().sub; }
  named_subt &get_named_sub() { return write().named_sub; } // DANGEROUS
  const named_subt &get_named_sub() const { return read().named_sub; }
  named_subt &get_comments() { return write().comments; } // DANGEROUS
  const named_subt &get_comments() const { return read().comments; }

  std::size_t hash() const;
  std::size_t full_hash() const;

  bool full_eq(const irept &other) const;

  std::string pretty(unsigned indent=0, unsigned max_indent=0) const;

protected:
  static bool is_comment(const irep_namet &name)
  { return !name.empty() && name[0]=='#'; }

private:
  class dt
  #ifdef SHARING
    :public small_pointeet
  #endif
  {
  public:
    irep_idt data;
    named_subt named_sub;
    named_subt comments;
    subt sub;

    #ifdef HASH_CODE
    mutable std::size_t hash_code=0;
    #endif

    void clear()
    {
      data.clear();
      named_sub.clear();
      comments.clear();
      sub.clear();
      #ifdef HASH_CODE
      hash_code=0;
      #endif
    }
  };

#ifdef SHARING
  small_shared_ptrt<dt> data=make_small_shared_ptr<dt>();
#else
  dt data;
#endif

public:
  const dt &read() const
  {
    #ifdef SHARING
    assert(data);
    return *data;
    #else
    return data;
    #endif
  }

private:
  dt &write()
  {
    #ifdef SHARING
    assert(data);
    if(data.use_count()!=1)
    {
      data=make_small_shared_ptr<dt>(*data);
    }
    #ifdef HASH_CODE
    data->hash_code=0;
    #endif
    return *data;
    #else
    return data;
    #endif
  }
};

// NOLINTNEXTLINE(readability/identifiers)
struct irep_hash
{
  std::size_t operator()(const irept &irep) const
  {
    return irep.hash();
  }
};

// NOLINTNEXTLINE(readability/identifiers)
struct irep_full_hash
{
  std::size_t operator()(const irept &irep) const
  {
    return irep.full_hash();
  }
};

// NOLINTNEXTLINE(readability/identifiers)
struct irep_full_eq
{
  bool operator()(const irept &i1, const irept &i2) const
  {
    return i1.full_eq(i2);
  }
};

#endif // CPROVER_UTIL_IREP_H

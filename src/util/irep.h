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
#define USE_MOVE
// #define SUB_IS_LIST

#ifdef SUB_IS_LIST
#include <list>
#else
#include <map>
#endif

#ifdef USE_DSTRING
using irep_idt = dstringt;
using irep_namet = dstringt;
// NOLINTNEXTLINE(readability/identifiers)
using irep_id_hash = dstring_hash;
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
  using subt = std::vector<irept>;

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

  explicit irept(const irep_idt &_id)
#ifdef SHARING
    :data(&empty_d)
#endif
  {
    id(_id);
  }

  #ifdef SHARING
  // constructor for blank irep
  irept():data(&empty_d)
  {
  }

  // copy constructor
  irept(const irept &irep):data(irep.data)
  {
    if(data!=&empty_d)
    {
      assert(data->ref_count!=0);
      data->ref_count++;
      #ifdef IREP_DEBUG
      std::cout << "COPY " << data << " " << data->ref_count << '\n';
      #endif
    }
  }

  #ifdef USE_MOVE
  // Copy from rvalue reference.
  // Note that this does avoid a branch compared to the
  // standard copy constructor above.
  irept(irept &&irep):data(irep.data)
  {
    #ifdef IREP_DEBUG
    std::cout << "COPY MOVE\n";
    #endif
    irep.data=&empty_d;
  }
  #endif

  irept &operator=(const irept &irep)
  {
    #ifdef IREP_DEBUG
    std::cout << "ASSIGN\n";
    #endif

    // Ordering is very important here!
    // Consider self-assignment, which may destroy 'irep'
    dt *irep_data=irep.data;
    if(irep_data!=&empty_d)
      irep_data->ref_count++;

    remove_ref(data); // this may kill 'irep'
    data=irep_data;

    return *this;
  }

  #ifdef USE_MOVE
  // Note that the move assignment operator does avoid
  // three branches compared to standard operator above.
  irept &operator=(irept &&irep)
  {
    #ifdef IREP_DEBUG
    std::cout << "ASSIGN MOVE\n";
    #endif
    // we simply swap two pointers
    std::swap(data, irep.data);
    return *this;
  }
  #endif

  ~irept()
  {
    remove_ref(data);
  }

  #else
  irept()
  {
  }
  #endif

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

public:
  class dt
  {
  private:
    friend class irept;

    #ifdef SHARING
    unsigned ref_count;
    #endif

    irep_idt data;

    named_subt named_sub;
    named_subt comments;
    subt sub;

    #ifdef HASH_CODE
    mutable std::size_t hash_code;
    #endif

    void clear()
    {
      data.clear();
      sub.clear();
      named_sub.clear();
      comments.clear();
      #ifdef HASH_CODE
      hash_code=0;
      #endif
    }

    void swap(dt &d)
    {
      d.data.swap(data);
      d.sub.swap(sub);
      d.named_sub.swap(named_sub);
      d.comments.swap(comments);
      #ifdef HASH_CODE
      std::swap(d.hash_code, hash_code);
      #endif
    }

    #ifdef SHARING
    dt():ref_count(1)
      #ifdef HASH_CODE
         , hash_code(0)
      #endif
    {
    }
    #else
    dt()
      #ifdef HASH_CODE
      :hash_code(0)
      #endif
    {
    }
    #endif
  };

protected:
  #ifdef SHARING
  dt *data;
  static dt empty_d;

  static void remove_ref(dt *old_data);
  static void nonrecursive_destructor(dt *old_data);
  void detach();

public:
  const dt &read() const
  {
    return *data;
  }

  dt &write()
  {
    detach();
    #ifdef HASH_CODE
    data->hash_code=0;
    #endif
    return *data;
  }

  #else
  dt data;

public:
  const dt &read() const
  {
    return data;
  }

  dt &write()
  {
    #ifdef HASH_CODE
    data.hash_code=0;
    #endif
    return data;
  }
  #endif
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

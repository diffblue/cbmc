/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IREP_H
#define CPROVER_IREP_H

#include <vector>
#include <map>
#include <string>
#include <cassert>
#include <ostream>

#define USE_DSTRING
#define SHARING

#ifdef USE_DSTRING
#include "dstring.h"
#endif

#include "irep_ids.h"

#ifdef USE_DSTRING
typedef dstring irep_idt;
typedef dstring irep_namet;
typedef dstring_hash irep_id_hash;
#else
#include "string_hash.h"
typedef std::string irep_idt;
typedef std::string irep_namet;
typedef string_hash irep_id_hash;
#endif

extern inline const std::string &id2string(const irep_idt &d)
{
  #ifdef USE_DSTRING
  return as_string(d);
  #else
  return d;
  #endif
}

extern inline const std::string &name2string(const irep_namet &n)
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

/*! \brief Base class for tree-like data structures with sharing
*/
class irept
{
public:
  typedef std::vector<irept> subt;
  typedef std::map<irep_namet, irept> named_subt;

  inline bool is_nil() const { return id()==ID_nil; }
  inline bool is_not_nil() const { return id()!=ID_nil; }

  inline explicit irept(const irep_idt &_id):data(&empty_d)
  {
    id(_id);
  }

  #ifdef SHARING
  inline irept():data(&empty_d)
  {
  }

  inline irept(const irept &irep):data(irep.data)
  {
    if(data!=&empty_d)
    {
      assert(data->ref_count!=0);
      data->ref_count++;
      #ifdef IREP_DEBUG
      std::cout << "COPY " << data << " " << data->ref_count << std::endl;
      #endif
    }
  }

  inline irept &operator=(const irept &irep)
  {
    #ifdef IREP_DEBUG
    std::cout << "ASSIGN\n";
    #endif

    // Ordering is very important here!
    // Consider self-assignment, which may destroy 'irep'
    dt *irep_data=irep.data;
    if(irep_data!=&empty_d) irep_data->ref_count++;

    remove_ref(data); // this may kill 'irep'
    data=irep_data;

    return *this;
  }

  inline ~irept()
  {
    remove_ref(data);
    data=NULL;
  }
  #else
  inline irept()
  {
  }
  #endif

  inline const irep_idt &id() const
  { return read().data; }
  
  inline const std::string &id_string() const
  { return id2string(read().data); }

  inline void id(const irep_idt &_data)
  { write().data=_data; }

  const irept &find(const irep_namet &name) const;
  irept &add(const irep_namet &name);

  inline const std::string &get_string(const irep_namet &name) const
  {
    return id2string(get(name));
  }
  
  const irep_idt &get(const irep_namet &name) const;
  bool get_bool(const irep_namet &name) const;
  int get_int(const irep_namet &name) const;

  inline void set(const irep_namet &name, const irep_idt &value)
  { add(name).id(value); }
  
  void set(const irep_namet &name, const long value);
  void set(const irep_namet &name, const irept &irep);
  void remove(const irep_namet &name);
  void move_to_sub(irept &irep);
  void move_to_named_sub(const irep_namet &name, irept &irep);
  
  friend bool operator==(const irept &i1, const irept &i2);
   
  friend inline bool operator!=(const irept &i1, const irept &i2)
  { return !(i1==i2); }

  friend std::ostream& operator<< (std::ostream& out, const irept &irep);
  
  std::string to_string() const;
  
  inline void swap(irept &irep)
  {
    std::swap(irep.data, data);
  }

  friend bool operator<(const irept &i1, const irept &i2);
  friend bool ordering(const irept &i1, const irept &i2);

  int compare(const irept &i) const;
  
  void clear();

  inline void make_nil() { clear(); id(ID_nil); }
  
  inline subt &get_sub() { return write().sub; } // DANGEROUS
  inline const subt &get_sub() const { return read().sub; }
  inline named_subt &get_named_sub() { return write().named_sub; } // DANGEROUS
  inline const named_subt &get_named_sub() const { return read().named_sub; }
  inline named_subt &get_comments() { return write().comments; } // DANGEROUS
  inline const named_subt &get_comments() const { return read().comments; }
  
  size_t hash() const;
  size_t full_hash() const;
  
  friend bool full_eq(const irept &a, const irept &b);
  
  std::string pretty(unsigned indent=0, unsigned max_indent=0) const;
  
protected:
  inline static bool is_comment(const irep_namet &name)
  { return !name.empty() && name[0]=='#'; }

public:
  class dt
  {
  public:
    #ifdef SHARING
    unsigned ref_count;
    #endif

    #ifdef USE_DSTRING
    dstring data;
    #else
    std::string data;
    #endif

    named_subt named_sub;
    named_subt comments;
    subt sub;

    void clear()
    {
      #ifdef USE_DSTRING
      data.clear();
      #else
      data="";
      #endif
      sub.clear();
      named_sub.clear();
      comments.clear();
    }
    
    void swap(dt &d)
    {
      d.data.swap(data);
      d.sub.swap(sub);
      d.named_sub.swap(named_sub);
      d.comments.swap(comments);
    }
    
    #ifdef SHARING
    dt():ref_count(1)
    {
    }
    #else
    dt()
    {
    }
    #endif
  };
  
protected:
  #ifdef SHARING
  dt *data;
  static dt empty_d;
  
  void remove_ref(dt *old_data);  
  void detatch();

public:  
  inline const dt &read() const
  {
    return *data;
  }

  inline dt &write()
  {
    detatch();
    return *data;
  }
  
  void recursive_detatch();
  
  #else
  dt data;

public:
  inline const dt &read() const
  {
    return data;
  }

  inline dt &write()
  {
    return data;
  }
  #endif
};

struct irep_hash
{
  inline size_t operator()(const irept &irep) const { return irep.hash(); }
};

struct irep_full_hash
{
  inline size_t operator()(const irept &irep) const { return irep.full_hash(); }
};

struct irep_full_eq
{
  inline bool operator()(const irept &i1, const irept &i2) const 
  {
    return full_eq(i1, i2);
  }
};

const irept &get_nil_irep();

#endif

/*******************************************************************\

Module: String Storage

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STRINGDB_H
#define CPROVER_STRINGDB_H

#include <ostream>

#include <algorithm>
#include <string>

#include "hash_cont.h"
#include "string_hash.h"

typedef hash_set_cont<std::string, string_hash> dstring_storaget;

class stringdbt
{
public:
  stringdbt();
  
  typedef const std::string *reft;
  
  inline reft empty_ref() const
  {
    return &empty_string;
  }
  
  reft make_ref(const std::string &s)
  {
    if(s.empty()) return &empty_string;
    dstring_storaget::const_iterator it=storage.insert(s).first;
    return &(*it);
  }
  
  void output(std::ostream &out) const;
 
protected:
  dstring_storaget storage;
  std::string empty_string;
  friend class dstring;
};

extern stringdbt stringdb;

class dstring
{
public:
  // constructors
  
  inline dstring() // fast default initialization
  { ref=stringdb.empty_ref(); }

  inline dstring(const dstring &s)
  { ref=s.ref; }

  inline dstring(const std::string &s)
  { ref=stringdb.make_ref(s); }

  inline dstring(const char *s)
  { ref=stringdb.make_ref(s); }

  // destructor
  ~dstring()
  {
  }
  
  // string access
  inline const char *c_str() const
  { return as_string().c_str(); }
   
  inline char operator[](unsigned n) const
  { return as_string()[n]; }

  inline char at(unsigned n) const
  { return as_string()[n]; }
   
  inline unsigned length() const
  { return as_string().length(); }

  inline unsigned size() const
  { return as_string().size(); }

  inline bool empty() const
  { return ref==stringdb.empty_ref(); }

  // comparison

  bool operator< (const dstring &b) const { return as_string()< b.as_string(); }
  bool operator> (const dstring &b) const { return as_string()> b.as_string(); }
  bool operator<=(const dstring &b) const { return as_string()<=b.as_string(); }
  bool operator>=(const dstring &b) const { return as_string()>=b.as_string(); }

  // comparison with same type

  inline bool operator==(const dstring &b) const
  { return ref==b.ref; } // really fast equality testing

  inline bool operator!=(const dstring &b) const
  { return ref!=b.ref; } // really fast equality testing

  // comparison with other types

  bool operator==(const char *b) const { return as_string()==b; }
  bool operator!=(const char *b) const { return as_string()!=b; }
  bool operator< (const char *b) const { return as_string()< b; }
  bool operator> (const char *b) const { return as_string()> b; }
  bool operator<=(const char *b) const { return as_string()<=b; }
  bool operator>=(const char *b) const { return as_string()>=b; }

  bool operator==(const std::string &b) const { return as_string()==b; }
  bool operator!=(const std::string &b) const { return as_string()!=b; }
  bool operator< (const std::string &b) const { return as_string()< b; }
  bool operator> (const std::string &b) const { return as_string()> b; }
  bool operator<=(const std::string &b) const { return as_string()<=b; }
  bool operator>=(const std::string &b) const { return as_string()>=b; }
  
  int compare(const dstring &b) const
  {
    if(ref==b.ref) return 0; // equal
    return as_string().compare(b.as_string());
  }
  
  friend bool ordering(const dstring &a, const dstring &b)
  {
    return long(a.ref)<long(b.ref);
  }

  inline const std::string &as_string() const
  { return *ref; }
   
  // modifying
  
  inline void clear()
  { ref=stringdb.empty_ref(); }
   
  inline void swap(dstring &b)
  { stringdbt::reft t=ref; ref=b.ref; b.ref=t; }

  dstring &operator=(const dstring &b)
  { ref=b.ref; return *this; }
  
  friend std::ostream &operator<<(std::ostream &out, const dstring &a)
  {
    return out << a.as_string();
  }
  
  size_t hash() const
  {
    return (unsigned long)ref;
  }

protected:
  stringdbt::reft ref;
};

class dstring_ordering
{
public:
  bool operator()(const dstring &a, const dstring &b)
  {
    return ordering(a, b);
  }
};

size_t hash_string(const dstring &s);

struct dstring_hash
{
  size_t operator()(const dstring &s) const { return s.hash(); }
};

#endif

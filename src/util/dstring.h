/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_DSTRING_H
#define CPROVER_UTIL_DSTRING_H

#include <iosfwd>

#include "string_container.h"

// Marked final to disable inheritance.
// No virtual destructor, so runtime-polymorphic use would be unsafe.
class dstringt final
{
public:
  // this is safe for static objects
  #ifdef __GNUC__
  constexpr
  #endif
  dstringt():no(0)
  {
  }

  // this is safe for static objects
  #ifdef __GNUC__
  constexpr
  #endif
  static dstringt make_from_table_index(unsigned no)
  {
    return dstringt(no);
  }

  #if 0
  // This conversion allows the use of dstrings
  // in switch ... case statements.
  constexpr operator int() const { return no; }
  #endif

  // this one is not safe for static objects
  // NOLINTNEXTLINE(runtime/explicit)
  dstringt(const char *s):no(string_container[s])
  {
  }

  // this one is not safe for static objects
  // NOLINTNEXTLINE(runtime/explicit)
  dstringt(const std::string &s):no(string_container[s])
  {
  }

  // access

  bool empty() const
  {
    return no==0; // string 0 is exactly the empty string
  }

  char operator[](size_t i) const
  {
    return as_string()[i];
  }

  // the pointer is guaranteed to be stable
  const char *c_str() const
  {
    return as_string().c_str();
  }

  size_t size() const
  {
    return as_string().size();
  }

  // ordering -- not the same as lexicographical ordering

  bool operator< (const dstringt &b) const { return no<b.no; }

  // comparison with same type

  bool operator==(const dstringt &b) const
  { return no==b.no; } // really fast equality testing

  bool operator!=(const dstringt &b) const
  { return no!=b.no; } // really fast equality testing

  // comparison with other types

  bool operator==(const char *b) const { return as_string()==b; }
  bool operator!=(const char *b) const { return as_string()!=b; }

  bool operator==(const std::string &b) const { return as_string()==b; }
  bool operator!=(const std::string &b) const { return as_string()!=b; }
  bool operator<(const std::string &b) const { return as_string()<b; }
  bool operator>(const std::string &b) const { return as_string()>b; }
  bool operator<=(const std::string &b) const { return as_string()<=b; }
  bool operator>=(const std::string &b) const { return as_string()>=b; }

  int compare(const dstringt &b) const
  {
    if(no==b.no)
      return 0; // equal
    return as_string().compare(b.as_string());
  }

  // modifying

  void clear()
  { no=0; }

  void swap(dstringt &b)
  { unsigned t=no; no=b.no; b.no=t; }

  dstringt &operator=(const dstringt &b)
  { no=b.no; return *this; }

  // output

  std::ostream &operator<<(std::ostream &out) const
  {
    return out << as_string();
  }

  // non-standard

  unsigned get_no() const
  {
    return no;
  }

  size_t hash() const
  {
    return no;
  }

private:
  #ifdef __GNUC__
  constexpr
  #endif
  explicit dstringt(unsigned _no):no(_no)
  {
  }

  unsigned no;

  // the reference returned is guaranteed to be stable
  const std::string &as_string() const
  { return string_container.get_string(no); }
};

// the reference returned is guaranteed to be stable
inline const std::string &as_string(const dstringt &s)
{ return string_container.get_string(s.get_no()); }

// NOLINTNEXTLINE(readability/identifiers)
struct dstring_hash
{
  size_t operator()(const dstringt &s) const { return s.hash(); }
};

inline size_t hash_string(const dstringt &s)
{
  return s.hash();
}

inline std::ostream &operator<<(std::ostream &out, const dstringt &a)
{
  return a.operator<<(out);
}

#endif // CPROVER_UTIL_DSTRING_H

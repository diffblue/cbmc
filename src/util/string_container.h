/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Container for C-Strings

#ifndef CPROVER_UTIL_STRING_CONTAINER_H
#define CPROVER_UTIL_STRING_CONTAINER_H

#include <list>
#include <unordered_map>
#include <vector>

#include "string_hash.h"

struct string_ptrt
{
  const char *s;
  size_t len;

  const char *c_str() const
  {
    return s;
  }

  explicit string_ptrt(const char *_s);

  explicit string_ptrt(const std::string &_s):s(_s.c_str()), len(_s.size())
  {
  }

  bool operator==(const string_ptrt &other) const;
};

// NOLINTNEXTLINE(readability/identifiers)
class string_ptr_hash
{
public:
  size_t operator()(const string_ptrt s) const { return hash_string(s.s); }
};

class string_containert
{
public:
  unsigned operator[](const char *s)
  {
    return get(s);
  }

  unsigned operator[](const std::string &s)
  {
    return get(s);
  }

  // constructor and destructor
  string_containert();
  ~string_containert();

  // the pointer is guaranteed to be stable
  const char *c_str(size_t no) const
  {
    return string_vector[no]->c_str();
  }

  // the reference is guaranteed to be stable
  const std::string &get_string(size_t no) const
  {
    return *string_vector[no];
  }

protected:
  // the 'unsigned' ought to be size_t
  typedef std::unordered_map<string_ptrt, unsigned, string_ptr_hash>
    hash_tablet;
  hash_tablet hash_table;

  unsigned get(const char *s);
  unsigned get(const std::string &s);

  typedef std::list<std::string> string_listt;
  string_listt string_list;

  typedef std::vector<std::string *> string_vectort;
  string_vectort string_vector;
};

string_containert &get_string_container();

#endif // CPROVER_UTIL_STRING_CONTAINER_H

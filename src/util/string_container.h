/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef STRING_CONTAINER_H
#define STRING_CONTAINER_H

#include <list>
#include <vector>

#include "hash_cont.h"
#include "string_hash.h"

struct string_ptrt
{
  const char *s;
  unsigned len;
  
  inline const char *c_str() const
  {
    return s;
  }
  
  explicit string_ptrt(const char *_s);

  explicit string_ptrt(const std::string &_s):s(_s.c_str()), len(_s.size())
  {
  }

  friend bool operator==(const string_ptrt a, const string_ptrt b);
};

bool operator==(const string_ptrt a, const string_ptrt b);

class string_ptr_hash
{
public:
  size_t operator()(const string_ptrt s) const { return hash_string(s.s); }
};

class string_containert
{
public:
  inline unsigned operator[](const char *s)
  {
    return get(s);
  }
  
  inline unsigned operator[](const std::string &s)
  {
    return get(s);
  }
  
  // constructor and destructor
  string_containert();  
  ~string_containert();

  // the pointer is guaranteed to be stable  
  inline const char *c_str(unsigned no) const
  {
    return string_vector[no]->c_str();
  }
  
  // the reference is guaranteed to be stable
  inline const std::string &get_string(unsigned no) const
  {
    return *string_vector[no];
  }
  
protected:
  typedef hash_map_cont<string_ptrt, unsigned, string_ptr_hash> hash_tablet;
  hash_tablet hash_table;
  
  unsigned get(const char *s);
  unsigned get(const std::string &s);
  
  typedef std::list<std::string> string_listt;
  string_listt string_list;
  
  typedef std::vector<std::string *> string_vectort;
  string_vectort string_vector;
};

// an ugly global object
extern string_containert string_container;

#endif

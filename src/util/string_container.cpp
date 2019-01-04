/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Container for C-Strings

#include "string_container.h"

#include <cstring>

#include "narrow.h"

string_ptrt::string_ptrt(const char *_s):s(_s), len(strlen(_s))
{
}

bool string_ptrt::operator==(const string_ptrt &other) const
{
  if(len!=other.len)
    return false;

  return len==0 || memcmp(s, other.s, len)==0;
}

string_containert::~string_containert()
{
}

unsigned string_containert::get(const char *s)
{
  string_ptrt string_ptr(s);

  hash_tablet::iterator it=hash_table.find(string_ptr);

  if(it!=hash_table.end())
    return it->second;

  const unsigned r = narrow_cast<unsigned>(hash_table.size());

  // these are stable
  string_list.push_back(std::string(s));
  string_ptrt result(string_list.back());

  hash_table[result]=r;

  // these are not
  string_vector.push_back(&string_list.back());

  return r;
}

unsigned string_containert::get(const std::string &s)
{
  string_ptrt string_ptr(s);

  hash_tablet::iterator it=hash_table.find(string_ptr);

  if(it!=hash_table.end())
    return it->second;

  const unsigned r = narrow_cast<unsigned>(hash_table.size());

  // these are stable
  string_list.push_back(s);
  string_ptrt result(string_list.back());

  hash_table[result]=r;

  // these are not
  string_vector.push_back(&string_list.back());

  return r;
}

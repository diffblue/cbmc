/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include <cassert>
#include <cctype>

#include "string_utils.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string strip_string(const std::string &s)
{
  std::string::size_type n=s.length();

  // find first non-space char
  unsigned i;
  for(i=0; i<n; i++)
  {
    if(!std::isspace(s[i]))
      break;
  }
  if(i==n)
    return "";

  std::string::const_reverse_iterator r_it;
  for(r_it=s.rbegin(); std::isspace(*r_it); r_it++);

  unsigned j=std::distance(r_it, s.rend())-1;

  return s.substr(i, (j-i+1));
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void split_string(
  const std::string &s,
  char delim,
  std::vector<std::string> &result,
  bool strip,
  bool remove_empty)
{
  assert(result.empty());
  assert(!std::isspace(delim));

  if(s.empty())
  {
    result.push_back("");
    return;
  }

  std::string::size_type n=s.length();
  assert(n>0);

  unsigned start=0;
  unsigned i;

  for (i=0; i<n; i++)
  {
    if (s[i]==delim)
    {
      std::string new_s=s.substr(start, i-start);

      if(strip)
        new_s=strip_string(new_s);

      if(!remove_empty || !new_s.empty())
        result.push_back(new_s);
      start=i+1;
    }
  }

  std::string new_s=s.substr(start, n-start);

  if(strip)
    new_s=strip_string(new_s);

  if(!remove_empty || !new_s.empty())
    result.push_back(new_s);

  assert(!result.empty());
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void split_string(
  const std::string &s,
  char delim,
  std::string &left,
  std::string &right,
  bool strip)
{
  assert(!std::isspace(delim));

  std::vector<std::string> result;

  split_string(s, delim, result, strip);
  if(result.size()!=2)
    throw "split string did not generate exactly 2 parts";

  left=result[0];
  right=result[1];
}

/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include "string_utils.h"

#include <cassert>
#include <cctype>
#include <algorithm>

std::string strip_string(const std::string &s)
{
  auto pred=[](char c){ return std::isspace(c); };

  std::string::const_iterator left
    =std::find_if_not(s.begin(), s.end(), pred);
  if(left==s.end())
    return "";

  std::string::size_type i=std::distance(s.begin(), left);

  std::string::const_reverse_iterator right
    =std::find_if_not(s.rbegin(), s.rend(), pred);
  std::string::size_type j=std::distance(right, s.rend())-1;

  return s.substr(i, (j-i+1));
}

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

  std::string::size_type start=0;
  std::string::size_type i;

  for(i=0; i<n; i++)
  {
    if(s[i]==delim)
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

  if(result.empty())
    result.push_back("");
}

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

std::string trim_from_last_delimiter(
  const std::string &s,
  const char delim)
{
  std::string result="";
  const size_t index=s.find_last_of(delim);
  if(index!=std::string::npos)
    result=s.substr(0, index);
  return result;
}

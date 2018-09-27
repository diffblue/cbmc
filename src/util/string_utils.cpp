/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include "string_utils.h"
#include "invariant.h"

#include <cassert>
#include <cctype>
#include <algorithm>

/// Remove all whitespace characters from either end of a string. Whitespace
/// in the middle of the string is left unchanged
/// \param s: the string to strip
/// \return The stripped string
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

/// Given a string s, split into a sequence of substrings when separated by
/// specified delimiter.
/// \param s: The string to split up
/// \param delim: The character to use as the delimiter
/// \param [out] result: The sub strings. Must be empty.
/// \param strip: If true, strip_string will be used on each element, removing
/// whitespace from the beginning and end of each element
/// \param remove_empty: If true, all empty-string elements will be removed.
/// This is applied after strip so whitespace only elements will be removed if
/// both are set to true
void split_string(
  const std::string &s,
  char delim,
  std::vector<std::string> &result,
  bool strip,
  bool remove_empty)
{
  PRECONDITION(result.empty());
  // delim can't be a space character if using strip
  PRECONDITION(!std::isspace(delim) || !strip);

  if(s.empty())
  {
    result.push_back("");
    return;
  }

  std::string::size_type n=s.length();
  INVARIANT(n > 0, "Empty string case should already be handled");

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
  // delim can't be a space character if using strip
  PRECONDITION(!std::isspace(delim) || !strip);

  std::vector<std::string> result;

  split_string(s, delim, result, strip);
  CHECK_RETURN(result.size() == 2);

  left=result[0];
  right=result[1];
}

std::vector<std::string> split_string(
  const std::string &s,
  char delim,
  bool strip,
  bool remove_empty)
{
  std::vector<std::string> result;
  split_string(s, delim, result, strip, remove_empty);
  return result;
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

std::string escape(const std::string &s)
{
  std::string result;

  for(std::size_t i=0; i<s.size(); i++)
  {
    if(s[i]=='\\' || s[i]=='"')
      result+='\\';

    result+=s[i];
  }

  return result;
}

/// Replace all occurrences of a string inside a string
/// \param [out] str: string to search
/// \param from: string to replace
/// \param to: string to replace with
/// Copyright notice:
/// Attributed to Gauthier Boaglio
/// Source: https://stackoverflow.com/a/24315631/7501486
/// Used under MIT license
void replace_all(
  std::string &str,
  const std::string &from,
  const std::string &to)
{
  size_t start_pos = 0;
  while((start_pos = str.find(from, start_pos)) != std::string::npos)
  {
    str.replace(start_pos, from.length(), to);
    start_pos += to.length();
  }
}

/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include "string_utils.h"
#include "exception_utils.h"
#include "invariant.h"

#include <algorithm>
#include <cctype>
#include <iomanip>

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
    if(!remove_empty)
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

  if(!remove_empty && result.empty())
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

  std::vector<std::string> result = split_string(s, delim, strip);

  if(result.size() != 2)
  {
    throw deserialization_exceptiont{"expected string '" + s +
                                     "' to contain two substrings "
                                     "delimited by " +
                                     delim + " but has " +
                                     std::to_string(result.size())};
  }

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
  std::string result;
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

std::string escape_non_alnum(const std::string &to_escape)
{
  std::ostringstream escaped;
  for(auto &ch : to_escape)
  {
    // `ch` may have a negative value in the case of utf-8 encodings of
    // characters above unicode code point 127. The following line maps these
    // negative values to positive values in the 128-255 range, using a
    // `static_cast`. This is neccessary in order to avoid undefined behaviour
    // in `isalnum`. The positive values are then stored in an integer using a
    // widening initialisation so that the stream insertion operator prints them
    // as numbers rather than characters.
    const int uch{static_cast<unsigned char>(ch)};
    if(ch == '_')
      escaped << "__";
    else if(isalnum(uch))
      escaped << ch;
    else
      escaped << '_' << std::hex << std::setfill('0') << std::setw(2) << uch;
  }
  return escaped.str();
}
std::string capitalize(const std::string &str)
{
  if(str.empty())
    return str;
  std::string capitalized = str;
  capitalized[0] = toupper(capitalized[0]);
  return capitalized;
}

std::string wrap_line(
  const std::string &line,
  const std::size_t left_margin,
  const std::size_t width)
{
  return wrap_line(line.cbegin(), line.cend(), left_margin, width);
}

std::string wrap_line(
  std::string::const_iterator left,
  std::string::const_iterator right,
  const std::size_t left_margin,
  const std::size_t width)
{
  PRECONDITION(left_margin < width);

  const std::size_t column_width = width - left_margin;
  const std::string margin(left_margin, ' ');

  auto distance = std::distance(left, right);
  CHECK_RETURN(distance > 0);

  std::string result;

  if(static_cast<std::size_t>(distance) <= column_width)
  {
    result.append(margin);
    result.append(left, right);

    return result;
  }

  auto it_line_begin = left;

  do
  {
    // points to the first character past the current column
    auto it = it_line_begin + column_width;

    auto rit_r = std::reverse_iterator<decltype(it)>(it) - 1;
    auto rit_l = rit_r + column_width;

    auto rit_space = std::find(rit_r, rit_l, ' ');

    if(rit_space != rit_l)
    {
      auto it_space = rit_space.base() - 1;
      CHECK_RETURN(*it_space == ' ');

      result.append(margin);
      result.append(it_line_begin, it_space);
      result.append("\n");

      it_line_begin = it_space + 1;
    }
    else
    {
      // we have not found a space, thus cannot wrap this line
      result.clear();
      result.append(left, right);

      return result;
    }
  } while(static_cast<std::size_t>(std::distance(it_line_begin, right)) >
          column_width);

  result.append(margin);
  result.append(it_line_begin, right);

  return result;
}

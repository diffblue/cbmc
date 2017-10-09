/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/


#ifndef CPROVER_UTIL_STRING_UTILS_H
#define CPROVER_UTIL_STRING_UTILS_H

#include <ostream>
#include <string>
#include <vector>

std::string strip_string(const std::string &s);

void split_string(
  const std::string &s,
  char delim, // must not be a whitespace character
  std::vector<std::string> &result,
  bool strip=false, // strip whitespace from elements
  bool remove_empty=false); // remove empty elements

void split_string(
  const std::string &s,
  char delim,
  std::string &left,
  std::string &right,
  bool strip=false);

std::string trim_from_last_delimiter(
  const std::string &s,
  const char delim);

/// Prints items to an stream, separated by a constant delimiter
/// \tparam It An iterator type
/// \tparam Delimiter A delimiter type which supports printing to ostreams
/// \param os An ostream to write to
/// \param b Iterator pointing to first item to print
/// \param e Iterator pointing past last item to print
/// \param delimiter Object to print between each item in the iterator range
/// \return A reference to the ostream that was passed in
template<typename Stream, typename It, typename Delimiter>
Stream &join_strings(
  Stream &os,
  const It b,
  const It e,
  const Delimiter &delimiter)
{
  if(b==e)
  {
    return os;
  }
  os << *b;
  for(auto it=std::next(b); it!=e; ++it)
  {
    os << delimiter << *it;
  }
  return os;
}

#endif

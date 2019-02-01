/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/


#ifndef CPROVER_UTIL_STRING_UTILS_H
#define CPROVER_UTIL_STRING_UTILS_H

#include <iosfwd>
#include <string>
#include <vector>

std::string strip_string(const std::string &s);

void split_string(
  const std::string &s,
  char delim,
  std::vector<std::string> &result,
  bool strip = false,
  bool remove_empty = false);

void split_string(
  const std::string &s,
  char delim,
  std::string &left,
  std::string &right,
  bool strip=false);

std::vector<std::string> split_string(
  const std::string &s,
  char delim,
  bool strip = false,
  bool remove_empty = false);

std::string trim_from_last_delimiter(
  const std::string &s,
  const char delim);

/// Prints items to an stream, separated by a constant delimiter
/// \tparam It: An iterator type
/// \tparam Delimiter: A delimiter type which supports printing to ostreams
/// \param os: An ostream to write to
/// \param b: Iterator pointing to first item to print
/// \param e: Iterator pointing past last item to print
/// \param delimiter: Object to print between each item in the iterator range
/// \param transform_func: Transform to apply to the value returned by the
///   iterator
/// \return A reference to the ostream that was passed in
template <
  typename Stream,
  typename It,
  typename Delimiter,
  typename TransformFunc>
Stream &join_strings(
  Stream &&os,
  const It b,
  const It e,
  const Delimiter &delimiter,
  TransformFunc &&transform_func)
{
  if(b==e)
  {
    return os;
  }
  os << transform_func(*b);
  for(auto it=std::next(b); it!=e; ++it)
  {
    os << delimiter << transform_func(*it);
  }
  return os;
}

/// Prints items to an stream, separated by a constant delimiter
/// \tparam It: An iterator type
/// \tparam Delimiter: A delimiter type which supports printing to ostreams
/// \param os: An ostream to write to
/// \param b: Iterator pointing to first item to print
/// \param e: Iterator pointing past last item to print
/// \param delimiter: Object to print between each item in the iterator range
/// \return A reference to the ostream that was passed in
template <typename Stream, typename It, typename Delimiter>
Stream &
join_strings(Stream &&os, const It b, const It e, const Delimiter &delimiter)
{
  using value_type = decltype(*b);
  // Call auxiliary function with identity function
  return join_strings(
    os, b, e, delimiter, [](const value_type &x) { return x; });
}

/// Generic escaping of strings; this is not meant to be a particular
/// programming language.
std::string escape(const std::string &);

void replace_all(std::string &, const std::string &, const std::string &);

#endif

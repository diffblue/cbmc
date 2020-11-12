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

std::string capitalize(const std::string &str);

void split_string(
  const std::string &s,
  char delim,
  std::string &left,
  std::string &right,
  bool strip = false);

/// Given a string s, split into a sequence of substrings when separated by
/// specified delimiter.
/// \param s: The string to split up
/// \param delim: The character to use as the delimiter
/// \param strip: If true, strip_string will be used on each element, removing
///   whitespace from the beginning and end of each element
/// \param remove_empty: If true, all empty-string elements will be removed.
///   This is applied after strip so whitespace only elements will be removed if
///   both are set to true.
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

/// Replace non-alphanumeric characters with `_xx` escapes, where xx are hex
/// digits. Underscores are replaced by `__`.
/// \param to_escape: string to escape
/// \return string with non-alphanumeric characters escaped
std::string escape_non_alnum(const std::string &to_escape);

/// Wrap line at spaces to not extend past the right margin, and include given
/// padding with spaces to the left
///
/// The given string should not contain any newlines.
///
/// \param line: line to wrap, should not contain newlines
/// \param left_margin: each line will be padded to the left with `left_margin`
///   spaces
/// \param width: width of the resulting text, i.e., right margin
/// \return resulting string such that each line has length less or equal to
///   `width`, and each line includes `left_margin` spaces to the left; if the
///   given line cannot be wrapped (i.e., it cannot be broken up at spaces such
///   that every resulting line fits within the margin), the given line is
///   returned unchanged
std::string wrap_line(
  const std::string &line,
  const std::size_t left_margin = 0,
  const std::size_t width = 80);

/// Wrap line at spaces to not extend past the right margin, and include given
/// padding with spaces to the left
///
/// The given string should not contain any newlines.
///
/// \param left: iterator to beginning of string
/// \param right: iterator to end of string
/// \param left_margin: each line will be padded to the left with `left_margin`
///   spaces
/// \param width: width of the resulting text, i.e., right margin
/// \return resulting string such that each line has length less or equal to
///   `width`, and each line includes `left_margin` spaces to the left; if the
///   given line cannot be wrapped (i.e., it cannot be broken up at spaces such
///   that every resulting line fits within the margin), the given line is
///   returned unchanged
std::string wrap_line(
  const std::string::const_iterator left,
  const std::string::const_iterator right,
  const std::size_t left_margin = 0,
  const std::size_t width = 80);

#endif

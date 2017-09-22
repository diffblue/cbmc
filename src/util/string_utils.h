/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/


#ifndef CPROVER_UTIL_STRING_UTILS_H
#define CPROVER_UTIL_STRING_UTILS_H

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

#endif

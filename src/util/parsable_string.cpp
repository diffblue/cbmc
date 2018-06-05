// Copyright 2019 Diffblue Limited.

/// \file
/// A wrapper for strings that facilitates parsing

#include "parsable_string.h"

parsable_stringt
parsable_stringt::split_at_first(char separator, const char *failure_error)
{
  std::size_t pos = underlying.find(separator, start_pos);
  if(pos == std::string::npos)
    throw parse_exceptiont(failure_error);
  parsable_stringt result(underlying, start_pos, pos);
  start_pos = pos + 1;
  return result;
}

std::pair<parsable_stringt, char> parsable_stringt::split_at_first_of(
  const std::string &separators,
  const char *failure_error)
{
  std::size_t pos = underlying.find_first_of(separators, start_pos);
  if(pos == std::string::npos)
    throw parse_exceptiont(failure_error);
  parsable_stringt result(underlying, start_pos, pos);
  start_pos = pos + 1;
  return { result, underlying[pos] };
}

char parsable_stringt::get_first(const char *failure_error)
{
  if(empty())
    throw parse_exceptiont(failure_error);
  char result = underlying[start_pos];
  ++start_pos;
  return result;
}

bool parsable_stringt::starts_with(char c)
{
  return !empty() && underlying[start_pos] == c;
}

bool parsable_stringt::try_skip(char c)
{
  if(starts_with(c))
  {
    ++start_pos;
    return true;
  }
  return false;
}

void parsable_stringt::skip(char c, const char *failure_error)
{
  if(!try_skip(c))
    throw parse_exceptiont(failure_error);
}

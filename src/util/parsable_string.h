// Copyright 2019 Diffblue Limited.

/// \file
/// A wrapper for strings that facilitates parsing

#ifndef CPROVER_UTIL_PARSABLE_STRING_H
#define CPROVER_UTIL_PARSABLE_STRING_H

#include <stdexcept>
#include <string>

class parsable_stringt
{
private:
  const std::string &underlying;
  std::size_t start_pos;
  std::size_t after_end_pos;

  parsable_stringt(
    const std::string &underlying,
    std::size_t start_pos,
    std::size_t after_end_pos)
    : underlying(underlying), start_pos(start_pos), after_end_pos(after_end_pos)
  {
  }

public:
  /// Create an instance containing the whole of the given string
  /// \param underlying The string to wrap in the input
  // NOLINTNEXTLINE(runtime/explicit) - loses no information
  parsable_stringt(const std::string &underlying)
    : parsable_stringt(underlying, 0, underlying.size())
  {
  }

  /// Get the input before the given separator, skip past the separator
  /// \param separator The separator to look for
  /// \param failure_error The message of the parse_exceptiont to throw if the
  ///   separator character is not found
  /// \return The input before the separator
  parsable_stringt split_at_first(char separator, const char *failure_error);

  /// Get the input before the first of the given separators is found, skip
  ///   past the found separator
  /// \param separators A string consisting of all the separators to look for
  /// \param failure_error The message of the parse_exceptiont to throw if a
  ///   separator character is not found
  /// \return The input before the separator and the separator that was found
  std::pair<parsable_stringt, char>
  split_at_first_of(const std::string &separators, const char *failure_error);

  /// Test whether the input is empty
  /// \return true if the input is empty
  bool empty() const
  {
    return start_pos >= after_end_pos;
  }

  /// Get the character at the start of the input and move to the next character
  /// \param failure_error The message of the parse_exceptiont to throw if the
  ///   input is empty
  /// \return The character at the start of the input
  char get_first(const char *failure_error);

  /// Test whether the input starts with the given character without moving
  ///   forward in the input
  /// \param c The character to look for at the start of the input
  /// \return true if the given character is found
  bool starts_with(char c);

  /// Try to skip the given character at the front of the input
  /// \param c The character to skip
  /// \return true if the character was found at the start of the input
  bool try_skip(char c);

  /// Skip the given character at the front of the input
  /// \param c The character to skip
  /// \param failure_error The message of the parse_exceptiont to throw if the
  ///   character is not found
  /// \throws parse_exceptiont if the character is not found
  void skip(char c, const char *failure_error);

  /// Default string extraction
  /// \return The substring represented by this instance
  operator std::string() const
  {
    return underlying.substr(start_pos, after_end_pos - start_pos);
  }
};

/// An exception that is raised for parse errors.
class parse_exceptiont : public std::logic_error
{
public:
  explicit parse_exceptiont(const std::string &arg) : std::logic_error(arg)
  {
  }
};

#endif // CPROVER_UTIL_PARSABLE_STRING_H

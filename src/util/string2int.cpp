/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include "string2int.h"

#include <cstdlib>
#include <stdexcept>

#include "invariant.h"

unsigned safe_string2unsigned(const std::string &str, int base)
{
  auto converted = string2optional<unsigned>(str, base);
  CHECK_RETURN(converted.has_value());
  return *converted;
}

std::size_t safe_string2size_t(const std::string &str, int base)
{
  auto converted = string2optional<std::size_t>(str, base);
  CHECK_RETURN(converted.has_value());
  return *converted;
}

int unsafe_string2int(const std::string &str, int base)
{
  return narrow_cast<int>(std::strtoll(str.c_str(), nullptr, base));
}

unsigned unsafe_string2unsigned(const std::string &str, int base)
{
  return narrow_cast<unsigned>(std::strtoul(str.c_str(), nullptr, base));
}

std::size_t unsafe_string2size_t(const std::string &str, int base)
{
  return narrow_cast<std::size_t>(std::strtoull(str.c_str(), nullptr, base));
}

signed long long int unsafe_string2signedlonglong(
  const std::string &str,
  int base)
{
  return std::strtoll(str.c_str(), nullptr, false);
}

unsigned long long int unsafe_string2unsignedlonglong(
  const std::string &str,
  int base)
{
  return *string2optional<unsigned long long>(str, base);
}

std::optional<int> string2optional_int(const std::string &str, int base)
{
  return string2optional<int>(str, base);
}

std::optional<unsigned>
string2optional_unsigned(const std::string &str, int base)
{
  return string2optional<unsigned>(str, base);
}

std::optional<std::size_t>
string2optional_size_t(const std::string &str, int base)
{
  return string2optional<std::size_t>(str, base);
}

/*******************************************************************\

Module: Memory units

Author: Hannes Steffenhagen

\*******************************************************************/

#ifndef CPROVER_UTIL_MEMORY_UNITS_H
#define CPROVER_UTIL_MEMORY_UNITS_H

#include <cstddef>
#include <string>

class memory_sizet
{
public:
  static memory_sizet from_bytes(std::size_t bytes);

  memory_sizet();
  memory_sizet(const memory_sizet &);
  memory_sizet(memory_sizet &&);

  memory_sizet &operator=(const memory_sizet &);
  memory_sizet &operator=(memory_sizet &&) noexcept;

  memory_sizet &operator+=(const memory_sizet &);
  memory_sizet operator+(const memory_sizet &) const;

  std::size_t get_bytes() const;
  std::size_t get_kibibytes() const;
  std::size_t get_mebibytes() const;
  std::size_t get_gibibytes() const;
  std::string to_string() const;

  static const char *si_byte_symbol;
  static const char *si_kibibyte_symbol;
  static const char *si_mebibyte_symbol;
  static const char *si_gibibyte_symbol;

private:
  std::size_t bytes;
  explicit memory_sizet(std::size_t bytes);
};

#endif // CPROVER_UTIL_MEMORY_UNITS_H

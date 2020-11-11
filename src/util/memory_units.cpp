/*******************************************************************\

Module: Memory units

Author: Hannes Steffenhagen

\*******************************************************************/

#include "memory_units.h"

#include <sstream>

memory_sizet::memory_sizet() : bytes(0)
{
}
memory_sizet::memory_sizet(std::size_t bytes) : bytes(bytes)
{
}
memory_sizet::memory_sizet(const memory_sizet &other) : bytes(other.bytes)
{
}
memory_sizet::memory_sizet(memory_sizet &&other) : bytes(other.bytes)
{
}

memory_sizet &memory_sizet::operator=(const memory_sizet &other)
{
  bytes = other.bytes;
  return *this;
}

memory_sizet &memory_sizet::operator=(memory_sizet &&other) noexcept
{
  bytes = other.bytes;
  return *this;
}

memory_sizet memory_sizet::from_bytes(std::size_t bytes)
{
  return memory_sizet(bytes);
}

std::size_t memory_sizet::get_bytes() const
{
  return bytes;
}

std::size_t memory_sizet::get_kibibytes() const
{
  return bytes / 1024;
}

std::size_t memory_sizet::get_mebibytes() const
{
  return bytes / (1024 * 1024);
}

std::size_t memory_sizet::get_gibibytes() const
{
  return bytes / (1024 * 1024 * 1024);
}

std::string memory_sizet::to_string() const
{
  std::size_t remainder = get_bytes();
  std::ostringstream out;
  const std::size_t gib = remainder / (1024 * 1024 * 1024);
  remainder -= gib * 1024 * 1024 * 1024;
  if(gib > 0)
  {
    out << gib << si_gibibyte_symbol;
  }
  const std::size_t mib = remainder / (1024 * 1024);
  remainder -= mib * 1024 * 1024;
  if(mib > 0)
  {
    if(gib > 0)
    {
      out << ' ';
    }
    out << mib << si_mebibyte_symbol;
  }
  const std::size_t kib = remainder / 1024;
  remainder -= kib * 1024;
  if(kib > 0)
  {
    if(mib > 0 || gib > 0)
    {
      out << ' ';
    }
    out << kib << si_kibibyte_symbol;
  }
  if(gib > 0 || mib > 0 || kib > 0)
  {
    out << ' ';
  }
  out << remainder << si_byte_symbol;
  return out.str();
}

const char *memory_sizet::si_byte_symbol = "B";
const char *memory_sizet::si_kibibyte_symbol = "KiB";
const char *memory_sizet::si_mebibyte_symbol = "MiB";
const char *memory_sizet::si_gibibyte_symbol = "GiB";

memory_sizet &memory_sizet::operator+=(const memory_sizet &other)
{
  bytes += other.bytes;
  return *this;
}

memory_sizet memory_sizet::operator+(const memory_sizet &other) const
{
  return memory_sizet(*this) += other;
}

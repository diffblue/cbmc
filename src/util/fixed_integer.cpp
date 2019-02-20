/*******************************************************************\

Module: Fixed-width Integer Type

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Fixed-width Integer Type

#include <cstdlib>

#include "fixed_integer.h"
#include "invariant.h"

fixed_integert::fixed_integert(fixed_integert &&other)
  : encoding(other.encoding)
{
  if(stored_in_class())
    value = other.value;
  else
  {
    ptr = other.ptr;
    other.ptr = nullptr;
    other.encoding.width_in_bits = 0;
  }
}

fixed_integert::fixed_integert(const fixed_integert &other)
  : encoding(other.encoding)
{
  if(stored_in_class())
    value = other.value;
  else
  {
    auto size = ptr_size();
    ptr = new char[size];
    memcpy(ptr, other.ptr, size);
  }
}

bool fixed_integert::is_zero() const
{
  if(stored_in_class())
    return value == 0;
  else
  {
    auto size = ptr_size();
    for(std::size_t i = 0; i < size; i++)
      if(ptr[i] != 0)
        return false;
    return true;
  }
}

fixed_integert &fixed_integert::operator+=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
  {
    value += other.value;
    value &= mask();
  }
  else
  {
    UNIMPLEMENTED;
  }

  return *this;
}

fixed_integert &fixed_integert::operator-=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
  {
    value -= other.value;
    value &= mask();
  }
  else
  {
    UNIMPLEMENTED;
  }

  return *this;
}

fixed_integert &fixed_integert::operator*=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
  {
    value *= other.value;
    value &= mask();
  }
  else
  {
    UNIMPLEMENTED;
  }

  return *this;
}

fixed_integert &fixed_integert::operator/=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);
  PRECONDITION(!other.is_zero());

  if(stored_in_class())
  {
    value /= other.value;
  }
  else
  {
    UNIMPLEMENTED;
  }

  return *this;
}

fixed_integert &fixed_integert::operator%=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);
  PRECONDITION(!other.is_zero());

  if(stored_in_class())
  {
    value %= other.value;
  }
  else
  {
    UNIMPLEMENTED;
  }

  return *this;
}

fixed_integert &fixed_integert::operator^=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
    value ^= other.value;
  else
  {
    auto size = ptr_size();
    for(std::size_t i = 0; i < size; i++)
      ptr[i] ^= other.ptr[i];
  }

  return *this;
}

fixed_integert &fixed_integert::operator|=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
    value |= other.value;
  else
  {
    auto size = ptr_size();
    for(std::size_t i = 0; i < size; i++)
      ptr[i] |= other.ptr[i];
  }

  return *this;
}

fixed_integert &fixed_integert::operator&=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
    value &= other.value;
  else
  {
    auto size = ptr_size();
    for(std::size_t i = 0; i < size; i++)
      ptr[i] &= other.ptr[i];
  }

  return *this;
}

fixed_integert &fixed_integert::operator<<=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
  {
    value <<= other.value;
    value &= mask();
  }
  else
  {
    UNIMPLEMENTED;
  }

  return *this;
}

fixed_integert &fixed_integert::operator>>=(const fixed_integert &other)
{
  PRECONDITION(encoding == other.encoding);

  if(stored_in_class())
    value >>= other.value;
  else
  {
    UNIMPLEMENTED;
  }

  return *this;
}

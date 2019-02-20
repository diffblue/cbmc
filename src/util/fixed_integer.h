/*******************************************************************\

Module: Fixed-width Integer Type

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Fixed-width Integer Type

#ifndef CPROVER_UTIL_FIXED_INTEGER_H
#define CPROVER_UTIL_FIXED_INTEGER_H

#include <iosfwd>
#include <string>

class fixed_integert final
{
public:
  using kindt = enum { SIGNED, UNSIGNED };
  using datat = unsigned long long int;

  fixed_integert(kindt kind, std::size_t _width_in_bits)
    : encoding(kind == SIGNED, _width_in_bits)
  {
    if(!stored_in_class())
      ptr = new char[ptr_size()];
  }

  template <typename T>
  fixed_integert(T _value, kindt kind, std::size_t _width_in_bits)
    : fixed_integert(kind, _width_in_bits)
  {
    set_value(static_cast<datat>(_value));
  }

  ~fixed_integert()
  {
    if(!stored_in_class())
      delete[] ptr;
  }

  fixed_integert(fixed_integert &&);
  fixed_integert(const fixed_integert &);
  bool operator==(const fixed_integert &);
  bool operator!=(const fixed_integert &);
  bool operator<(const fixed_integert &);
  bool operator<=(const fixed_integert &);
  bool operator>(const fixed_integert &);
  bool operator>=(const fixed_integert &);

  void set_value(datat);

  fixed_integert &operator+=(const fixed_integert &);
  fixed_integert &operator-=(const fixed_integert &);
  fixed_integert &operator*=(const fixed_integert &);
  fixed_integert &operator/=(const fixed_integert &);
  fixed_integert &operator%=(const fixed_integert &);
  fixed_integert &operator^=(const fixed_integert &);
  fixed_integert &operator|=(const fixed_integert &);
  fixed_integert &operator&=(const fixed_integert &);
  fixed_integert &operator<<=(const fixed_integert &);
  fixed_integert &operator>>=(const fixed_integert &);

  bool is_zero() const;

protected:
  struct encodingt
  {
    encodingt(bool _is_signed, std::size_t _width_in_bits)
      : is_signed(_is_signed), width_in_bits(_width_in_bits)
    {
    }

    bool is_signed;
    std::size_t width_in_bits : sizeof(std::size_t) * 8 - 1;

    bool operator==(const encodingt &other) const
    {
      return is_signed == other.is_signed &&
             width_in_bits == other.width_in_bits;
    }
  } encoding;

  union {
    // either store the number directly,
    // or a pointer to dynamically allocated array
    datat value;
    char *ptr;
  };

  bool stored_in_class() const
  {
    return encoding.width_in_bits <= sizeof(datat) * 8;
  }

  std::size_t ptr_size() const
  {
    // this is division by 8, rounded up
    return (encoding.width_in_bits + 7) / 8;
  }

  datat mask() const
  {
    return (datat(1) << encoding.width_in_bits) - 1;
  }
};

#endif // CPROVER_UTIL_FIXEDINTEGER_H

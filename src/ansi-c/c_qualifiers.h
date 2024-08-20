/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_C_QUALIFIERS_H
#define CPROVER_ANSI_C_C_QUALIFIERS_H

#include <memory>
#include <string>

class typet;

class c_qualifierst
{
public:
  c_qualifierst()
  {
    clear();
  }

  explicit c_qualifierst(const typet &src)
  {
    clear();
    read(src);
  }

  virtual ~c_qualifierst() = default;

protected:
  c_qualifierst &operator=(const c_qualifierst &other);
public:
  virtual std::unique_ptr<c_qualifierst> clone() const;

  virtual void clear()
  {
    is_constant=false;
    is_volatile=false;
    is_restricted=false;
    is_atomic=false;
    is_ptr32=is_ptr64=false;
    is_transparent_union=false;
    is_nodiscard = false;
    is_noreturn=false;
  }

  // standard ones
  bool is_constant, is_volatile, is_restricted, is_atomic, is_noreturn,
    is_nodiscard;

  // MS Visual Studio extension
  bool is_ptr32, is_ptr64;

  // gcc extension
  bool is_transparent_union;

  // will likely add alignment here as well

  virtual std::string as_string() const;
  virtual void read(const typet &src);
  virtual void write(typet &src) const;

  static void clear(typet &dest);

  bool is_subset_of(const c_qualifierst &other) const
  {
    return (!is_constant || other.is_constant) &&
           (!is_volatile || other.is_volatile) &&
           (!is_restricted || other.is_restricted) &&
           (!is_atomic || other.is_atomic) && (!is_ptr32 || other.is_ptr32) &&
           (!is_ptr64 || other.is_ptr64) &&
           (!is_nodiscard || other.is_nodiscard) &&
           (!is_noreturn || other.is_noreturn);

    // is_transparent_union isn't checked
  }

  bool operator==(const c_qualifierst &other) const
  {
    return is_constant == other.is_constant &&
           is_volatile == other.is_volatile &&
           is_restricted == other.is_restricted &&
           is_atomic == other.is_atomic && is_ptr32 == other.is_ptr32 &&
           is_ptr64 == other.is_ptr64 &&
           is_transparent_union == other.is_transparent_union &&
           is_nodiscard == other.is_nodiscard &&
           is_noreturn == other.is_noreturn;
  }

  bool operator!=(const c_qualifierst &other) const
  {
    return !(*this == other);
  }

  c_qualifierst &operator+=(const c_qualifierst &other)
  {
    is_constant |= other.is_constant;
    is_volatile |= other.is_volatile;
    is_restricted |= other.is_restricted;
    is_atomic |= other.is_atomic;
    is_ptr32 |= other.is_ptr32;
    is_ptr64 |= other.is_ptr64;
    is_transparent_union |= other.is_transparent_union;
    is_nodiscard |= other.is_nodiscard;
    is_noreturn |= other.is_noreturn;
    return *this;
  }

  virtual std::size_t count() const
  {
    return is_constant + is_volatile + is_restricted + is_atomic + is_ptr32 +
           is_ptr64 + is_nodiscard + is_noreturn;
  }
};

#endif // CPROVER_ANSI_C_C_QUALIFIERS_H

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_QUALIFIERS_H
#define CPROVER_ANSI_C_C_QUALIFIERS_H

#include <iosfwd>

#include <util/expr.h>

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

  void clear()
  {
    is_constant=false;
    is_volatile=false;
    is_restricted=false;
    is_atomic=false;
    is_ptr32=is_ptr64=false;
    is_transparent_union=false;
    is_noreturn=false;
  }

  // standard ones
  bool is_constant, is_volatile, is_restricted, is_atomic, is_noreturn;

  // MS Visual Studio extension
  bool is_ptr32, is_ptr64;

  // gcc extension
  bool is_transparent_union;

  // will likely add alignment here as well

  std::string as_string() const;
  void read(const typet &src);
  void write(typet &src) const;

  static void clear(typet &dest);

  bool is_subset_of(const c_qualifierst &q) const
  {
    return (!is_constant || q.is_constant) &&
           (!is_volatile || q.is_volatile) &&
           (!is_restricted || q.is_restricted) &&
           (!is_atomic || q.is_atomic) &&
           (!is_ptr32 || q.is_ptr32) &&
           (!is_ptr64 || q.is_ptr64) &&
           (!is_noreturn || q.is_noreturn);

    // is_transparent_union isn't checked
  }

  bool operator==(const c_qualifierst &other) const
  {
    return is_constant==other.is_constant &&
           is_volatile==other.is_volatile &&
           is_restricted==other.is_restricted &&
           is_atomic==other.is_atomic &&
           is_ptr32==other.is_ptr32 &&
           is_ptr64==other.is_ptr64 &&
           is_transparent_union==other.is_transparent_union &&
           is_noreturn==other.is_noreturn;
  }

  bool operator!=(const c_qualifierst &other) const
  {
    return !(*this==other);
  }

  c_qualifierst &operator += (
    const c_qualifierst &b)
  {
    is_constant|=b.is_constant;
    is_volatile|=b.is_volatile;
    is_restricted|=b.is_restricted;
    is_atomic|=b.is_atomic;
    is_ptr32|=b.is_ptr32;
    is_ptr64|=b.is_ptr64;
    is_transparent_union|=b.is_transparent_union;
    is_noreturn|=b.is_noreturn;
    return *this;
  }

  unsigned count() const
  {
    return is_constant+is_volatile+is_restricted+is_atomic+
           is_ptr32+is_ptr64+is_noreturn;
  }
};

std::ostream &operator << (std::ostream &, const c_qualifierst &);

#endif // CPROVER_ANSI_C_C_QUALIFIERS_H

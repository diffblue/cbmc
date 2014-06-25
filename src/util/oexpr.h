/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_OEXPR_H
#define CPROVER_OEXPR_H

#include "expr.h"
#include "std_types.h"

class oexprt:public exprt
{
public:
  explicit inline oexprt(const exprt &src):exprt(src)
  {
  }

  inline oexprt(const irep_idt &_id, const typet &_type):exprt(_id, _type)
  {
  }

  inline oexprt(
    const exprt &a, const irep_idt &_id, const exprt &b,
    const typet &_type):exprt(_id, _type)
  {
    copy_to_operands(a, b);
  }

  inline oexprt(
    const irep_idt &_id, const exprt &a,
    const typet &_type):exprt(_id, _type)
  {
    copy_to_operands(a);
  }
  
  inline oexprt operator[](const exprt &_index) const
  {
    return oexprt(*this, ID_index, _index, type().subtype());
  }
};

inline oexprt operator+(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_plus, b, a.type());
}

inline oexprt operator-(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_minus, b, a.type());
}

inline oexprt operator-(const exprt &a)
{
  return oexprt(ID_unary_minus, a, a.type());
}

inline exprt operator*(const exprt &a, const oexprt &b)
{
  return oexprt(a, ID_mult, b, a.type());
}

inline exprt operator*(const exprt &a)
{
  return oexprt(ID_dereference, a, a.type().subtype());
}

inline oexprt operator/(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_div, b, a.type());
}

inline oexprt operator%(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_mod, b, a.type());
}

inline oexprt operator&&(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_and, b, bool_typet());
}

inline oexprt operator||(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_or, b, bool_typet());
}

inline oexprt operator&(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_bitand, b, a.type());
}

inline oexprt operator|(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_bitor, b, a.type());
}

inline oexprt operator~(const exprt &a)
{
  return oexprt(ID_bitnot, a, a.type());
}

inline oexprt operator>>(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_shr, b, a.type());
}

inline oexprt operator<<(const exprt &a, const exprt &b)
{
  return oexprt(a, ID_shl, b, a.type());
}

inline oexprt operator==(const oexprt &a, const oexprt &b)
{
  return oexprt(a, ID_equal, b, bool_typet());
}

inline oexprt operator!=(const oexprt &a, const oexprt &b)
{
  return oexprt(a, ID_notequal, b, bool_typet());
}

inline oexprt operator!(const oexprt &a)
{
  return oexprt(ID_not, a, bool_typet());
}

inline oexprt operator<(const oexprt &a, const oexprt &b)
{
  return oexprt(a, ID_lt, b, bool_typet());
}

inline oexprt operator>(const oexprt &a, const oexprt &b)
{
  return oexprt(a, ID_gt, b, bool_typet());
}

inline oexprt operator<=(const oexprt &a, const oexprt &b)
{
  return oexprt(a, ID_le, b, bool_typet());
}

inline oexprt operator>=(const oexprt &a, const oexprt &b)
{
  return oexprt(a, ID_ge, b, bool_typet());
}

static inline oexprt ite(const oexprt &cond, const oexprt &a, const oexprt &b)
{
  oexprt result(ID_if, a.type());
  result.copy_to_operands(cond, a, b);
  return result;
}

static inline oexprt typecast(const oexprt &a, const typet &t)
{
  return oexprt(ID_typecast, a, t);
}

#endif

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_TYPECAST_H
#define CPROVER_ANSI_C_C_TYPECAST_H

#include <util/namespace.h>
#include <util/expr.h>

// try a type cast from expr.type() to type
//
// false: typecast successfull, expr modified
// true:  typecast failed

bool check_c_implicit_typecast(
  const typet &src_type,
  const typet &dest_type);

bool check_c_implicit_typecast(
  const typet &src_type,
  const typet &dest_type,
  const namespacet &ns);

bool c_implicit_typecast(
  exprt &expr,
  const typet &dest_type,
  const namespacet &ns);

bool c_implicit_typecast_arithmetic(
  exprt &expr1, exprt &expr2,
  const namespacet &ns);

class c_typecastt
{
public:
  c_typecastt(const namespacet &_ns):ns(_ns)
  {
  }

  virtual ~c_typecastt()
  {
  }

  virtual void implicit_typecast(
    exprt &expr,
    const typet &type);

  virtual void implicit_typecast_arithmetic(
    exprt &expr);

  virtual void implicit_typecast_arithmetic(
    exprt &expr1,
    exprt &expr2);
  
  std::list<std::string> errors;
  std::list<std::string> warnings;

protected:
  const namespacet &ns;
  
  // these are in promotion order

  enum c_typet { BOOL,
                 CHAR, UCHAR,
                 SHORT, USHORT,
                 INT, UINT,
                 LONG, ULONG,
                 LONGLONG, ULONGLONG,
                 LARGE_SIGNED_INT, LARGE_UNSIGNED_INT,
                 INTEGER, // these are unbounded integers
                 SINGLE, DOUBLE, LONGDOUBLE, FLOAT128, // float
                 RATIONAL, REAL, // these are infinite precision
                 COMPLEX,
                 VOIDPTR, PTR, OTHER };

  c_typet get_c_type(const typet &type) const;

  void implicit_typecast_arithmetic(
    exprt &expr,
    c_typet c_type);
  
  typet follow_with_qualifiers(const typet &src);

  // after follow_with_qualifiers
  virtual void implicit_typecast_followed(
    exprt &expr,
    const typet &src_type,
    const typet &orig_dest_type,
    const typet &dest_type);

  void do_typecast(exprt &dest, const typet &type);

  c_typet minimum_promotion(const typet &type) const;
};

#endif

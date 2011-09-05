/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BYTE_OPERATORS_H
#define CPROVER_BYTE_OPERATORS_H

/*! \file util/byte_operators.h
 * \brief Expression classes for byte-level operators
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include <expr.h>

/*! \brief TO_BE_DOCUMENTED
*/
class byte_extractt:public exprt
{
public:
  explicit inline byte_extractt(irep_idt _id):exprt(_id)
  {
    operands().resize(2);
  }

  inline exprt &op() { return op0(); }
  inline exprt &offset() { return op1(); }

  inline const exprt &op() const { return op0(); }
  inline const exprt &offset() const { return op1(); }
};

/*! \brief TO_BE_DOCUMENTED
*/
class byte_extract_little_endiant:public byte_extractt
{
public:
  inline byte_extract_little_endiant():byte_extractt(ID_byte_extract_little_endian)
  {
  }
};

extern inline const byte_extract_little_endiant &to_byte_extract_little_endian(const exprt &expr)
{
  assert(expr.id()==ID_byte_extract_little_endian && expr.operands().size()==2);
  return static_cast<const byte_extract_little_endiant &>(expr);
}

extern inline byte_extract_little_endiant &to_byte_extract_little_endian(exprt &expr)
{
  assert(expr.id()==ID_byte_extract_little_endian && expr.operands().size()==2);
  return static_cast<byte_extract_little_endiant &>(expr);
}

/*! \brief TO_BE_DOCUMENTED
*/
class byte_extract_big_endiant:public byte_extractt
{
public:
  inline byte_extract_big_endiant():byte_extractt(ID_byte_extract_big_endian)
  {
  }
};

extern inline const byte_extract_big_endiant &to_byte_extract_big_endian(const exprt &expr)
{
  assert(expr.id()==ID_byte_extract_big_endian && expr.operands().size()==2);
  return static_cast<const byte_extract_big_endiant &>(expr);
}

extern inline byte_extract_big_endiant &to_byte_extract_big_endian(exprt &expr)
{
  assert(expr.id()==ID_byte_extract_big_endian && expr.operands().size()==2);
  return static_cast<byte_extract_big_endiant &>(expr);
}

/*! \brief TO_BE_DOCUMENTED
*/
class byte_updatet:public exprt
{
public:
  explicit inline byte_updatet(irep_idt _id):exprt(_id)
  {
    operands().resize(3);
  }

  inline exprt &op() { return op0(); }
  inline exprt &offset() { return op1(); }
  inline exprt &value() { return op2(); }

  inline const exprt &op() const { return op0(); }
  inline const exprt &offset() const { return op1(); }
  inline const exprt &value() const { return op2(); }
};

/*! \brief TO_BE_DOCUMENTED
*/
class byte_update_little_endiant:public byte_updatet
{
public:
  inline byte_update_little_endiant():byte_updatet(ID_byte_update_little_endian)
  {
  }
};

extern inline const byte_update_little_endiant &to_byte_update_little_endian(const exprt &expr)
{
  assert(expr.id()==ID_byte_update_little_endian && expr.operands().size()==3);
  return static_cast<const byte_update_little_endiant &>(expr);
}

extern inline byte_update_little_endiant &to_byte_update_little_endian(exprt &expr)
{
  assert(expr.id()==ID_byte_update_little_endian && expr.operands().size()==3);
  return static_cast<byte_update_little_endiant &>(expr);
}

/*! \brief TO_BE_DOCUMENTED
*/
class byte_update_big_endiant:public byte_updatet
{
public:
  inline byte_update_big_endiant():byte_updatet(ID_byte_update_big_endian)
  {
  }
};

extern inline const byte_update_big_endiant &to_byte_update_big_endian(const exprt &expr)
{
  assert(expr.id()==ID_byte_update_big_endian && expr.operands().size()==3);
  return static_cast<const byte_update_big_endiant &>(expr);
}

extern inline byte_update_big_endiant &to_byte_update_big_endian(exprt &expr)
{
  assert(expr.id()==ID_byte_update_big_endian && expr.operands().size()==3);
  return static_cast<byte_update_big_endiant &>(expr);
}

#endif

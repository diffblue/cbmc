/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Logic

#ifndef CPROVER_SOLVERS_FLATTENING_POINTER_LOGIC_H
#define CPROVER_SOLVERS_FLATTENING_POINTER_LOGIC_H

#include <util/mp_arith.h>
#include <util/expr.h>
#include <util/numbering.h>

class namespacet;
class pointer_typet;

class pointer_logict
{
public:
  // this numbers the objects
  typedef hash_numbering<exprt, irep_hash> objectst;
  objectst objects;

  struct pointert
  {
    std::size_t object;
    mp_integer offset;

    pointert()
    {
    }

    pointert(std::size_t _obj, mp_integer _off):object(_obj), offset(_off)
    {
    }
  };

  // converts an (object,offset) pair to an expression
  exprt pointer_expr(
    const pointert &pointer,
    const pointer_typet &type) const;

  // converts an (object,0) pair to an expression
  exprt pointer_expr(
    std::size_t object,
    const pointer_typet &type) const;

  ~pointer_logict();
  explicit pointer_logict(const namespacet &_ns);

  std::size_t add_object(const exprt &expr);

  // number of NULL object
  std::size_t get_null_object() const
  {
    return null_object;
  }

  // number of INVALID object
  std::size_t get_invalid_object() const
  {
    return invalid_object;
  }

  bool is_dynamic_object(const exprt &expr) const;

  void get_dynamic_objects(std::vector<std::size_t> &objects) const;

protected:
  const namespacet &ns;
  std::size_t null_object, invalid_object;

  exprt pointer_expr(
    const mp_integer &offset,
    const exprt &object) const;
};

#endif // CPROVER_SOLVERS_FLATTENING_POINTER_LOGIC_H

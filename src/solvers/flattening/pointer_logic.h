/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_LOGIC_H
#define CPROVER_POINTER_LOGIC_H

#include <mp_arith.h>
#include <hash_cont.h>
#include <expr.h>
#include <numbering.h>

#define BV_ADDR_BITS 8

class pointer_logict
{
public:
  // this numbers the objects
  typedef hash_numbering<exprt, irep_hash> objectst;
  objectst objects;

  struct pointert
  {
    unsigned object;
    mp_integer offset;
    
    pointert()
    {
    }
    
    pointert(unsigned _obj, mp_integer _off):object(_obj), offset(_off)
    {
    }
  };
  
  // converts an (object,offset) pair to an expression
  exprt pointer_expr(
    const pointert &pointer,
    const typet &type) const;

  // converts an (object,0) pair to an expression
  exprt pointer_expr(
    unsigned object,
    const typet &type) const;
    
  ~pointer_logict();
  explicit pointer_logict(const namespacet &_ns);
  
  unsigned add_object(const exprt &expr);

  // number of NULL object  
  unsigned get_null_object() const
  {
    return null_object;
  }

  // number of INVALID object  
  unsigned get_invalid_object() const
  {
    return invalid_object;
  }
  
  bool is_dynamic_object(const exprt &expr) const;
  
  void get_dynamic_objects(std::vector<unsigned> &objects) const;

protected:
  const namespacet &ns;
  unsigned null_object, invalid_object;  

  exprt pointer_expr(
    const mp_integer &offset,
    const exprt &object) const;

  exprt object_rec(
    const mp_integer &offset,
    const typet &pointer_type,
    const exprt &src) const;
};

#endif

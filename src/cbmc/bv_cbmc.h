/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_BV_CBMC_H
#define CPROVER_CBMC_BV_CBMC_H

#include <solvers/flattening/bv_pointers.h>

class bv_cbmct:public bv_pointerst
{
public:
  bv_cbmct(
    const namespacet &_ns,
    propt &_prop):bv_pointerst(_ns, _prop) { }
  virtual ~bv_cbmct() { }

protected:
  // overloading
  virtual void convert_bitvector(const exprt &expr, bvt &bv); // no cache

  virtual void convert_waitfor(const exprt &expr, bvt &bv);
  virtual void convert_waitfor_symbol(const exprt &expr, bvt &bv);
};

#endif

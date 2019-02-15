/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H
#define CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H


#include "boolbv.h"
#include "pointer_logic.h"

class bv_pointerst:public boolbvt
{
public:
  bv_pointerst(
    const namespacet &_ns,
    propt &_prop,
    message_handlert &message_handler);

  void post_process() override;

protected:
  pointer_logict pointer_logic;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef boolbvt SUB;

  unsigned object_bits, offset_bits, bits;

  void encode(std::size_t object, bvt &bv);

  virtual bvt convert_pointer_type(const exprt &expr);

  virtual void add_addr(const exprt &expr, bvt &bv);

  // overloading
  literalt convert_rest(const exprt &expr) override;
  bvt convert_bitvector(const exprt &expr) override; // no cache

  exprt bv_get_rec(
    const exprt &expr,
    const bvt &bv,
    const std::vector<bool> &unknown,
    std::size_t offset,
    const typet &type) const override;

  bool convert_address_of_rec(
    const exprt &expr,
    bvt &bv);

  void offset_arithmetic(bvt &bv, const mp_integer &x);
  void offset_arithmetic(bvt &bv, const mp_integer &factor, const exprt &index);
  void offset_arithmetic(
    bvt &bv, const mp_integer &factor, const bvt &index_bv);

  struct postponedt
  {
    bvt bv, op;
    exprt expr;
  };

  typedef std::list<postponedt> postponed_listt;
  postponed_listt postponed_list;

  void do_postponed(const postponedt &postponed);
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H

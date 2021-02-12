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
    message_handlert &message_handler,
    bool get_array_constraints = false);

  void post_process() override;

protected:
  pointer_logict pointer_logic;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef boolbvt SUB;

  typedef std::map<std::size_t, bvt> pointer_bitst;
  pointer_bitst pointer_bits;
  bool need_address_bounds;

  void encode(std::size_t object, bvt &bv);

  virtual bvt convert_pointer_type(const exprt &expr);

  virtual void add_addr(const exprt &expr, bvt &bv);

  // overloading
  literalt convert_rest(const exprt &expr) override;
  bvt convert_bitvector(const exprt &expr) override; // no cache

  exprt bv_get_rec(
    const exprt &expr,
    const bvt &bv,
    std::size_t offset,
    const typet &type) const override;

  bool convert_address_of_rec(
    const exprt &expr,
    bvt &bv);

  void offset_arithmetic(bvt &bv, const mp_integer &x);
  void offset_arithmetic(bvt &bv, const mp_integer &factor, const exprt &index);

  struct postponedt
  {
    bvt bv, op;
    exprt expr;
  };

  typedef std::list<postponedt> postponed_listt;
  postponed_listt postponed_list;

  void do_postponed_non_typecast(const postponedt &postponed);
  typedef std::map<std::size_t, std::pair<bvt, bvt>> bounds_mapt;
  void encode_object_bounds(bounds_mapt &dest);
  void
  do_postponed_typecast(const postponedt &postponed, const bounds_mapt &bounds);

  void object_bv(bvt &bv, const pointer_typet &type) const
  {
    bv.resize(boolbv_width.get_object_width(type));
  }

  void offset_bv(bvt &bv, const pointer_typet &type) const
  {
    bv.erase(bv.begin(), bv.begin() + boolbv_width.get_object_width(type));
    bv.resize(boolbv_width.get_offset_width(type));
  }

  void address_bv(bvt &bv, const pointer_typet &type) const
  {
    bv.erase(
      bv.begin(),
      bv.begin() + boolbv_width.get_object_width(type) +
        boolbv_width.get_offset_width(type));
  }
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H

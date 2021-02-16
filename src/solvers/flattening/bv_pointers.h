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

  std::size_t boolbv_width(const typet &type) const override
  {
    return bv_pointers_width(type);
  }

  endianness_mapt
  endianness_map(const typet &type, bool little_endian) const override;

protected:
  pointer_logict pointer_logic;

  class bv_pointers_widtht : public boolbv_widtht
  {
  public:
    explicit bv_pointers_widtht(const namespacet &_ns) : boolbv_widtht(_ns)
    {
    }

    std::size_t operator()(const typet &type) const override;

    std::size_t get_object_width(const pointer_typet &type) const;
    std::size_t get_offset_width(const pointer_typet &type) const;
    std::size_t get_address_width(const pointer_typet &type) const;
  };
  bv_pointers_widtht bv_pointers_width;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef boolbvt SUB;

  void encode(std::size_t object, const pointer_typet &type, bvt &bv) const;

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

  void
  offset_arithmetic(const pointer_typet &type, bvt &bv, const mp_integer &x);
  void offset_arithmetic(
    const pointer_typet &type,
    bvt &bv,
    const mp_integer &factor,
    const exprt &index);
  void offset_arithmetic(
    const pointer_typet &type,
    bvt &bv,
    const mp_integer &factor,
    const bvt &index_bv);

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

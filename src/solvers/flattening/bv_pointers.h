/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H
#define CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H

#include <util/nodiscard.h>

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

  NODISCARD
  bvt encode(std::size_t object, const pointer_typet &type) const;

  virtual bvt convert_pointer_type(const exprt &expr);

  NODISCARD
  virtual bvt add_addr(const exprt &expr);

  // overloading
  literalt convert_rest(const exprt &expr) override;
  bvt convert_bitvector(const exprt &expr) override; // no cache

  exprt bv_get_rec(
    const exprt &expr,
    const bvt &bv,
    std::size_t offset,
    const typet &type) const override;

  NODISCARD
  optionalt<bvt> convert_address_of_rec(const exprt &expr);

  NODISCARD
  bvt offset_arithmetic(
    const pointer_typet &type,
    const bvt &bv,
    const mp_integer &x);
  NODISCARD
  bvt offset_arithmetic(
    const pointer_typet &type,
    const bvt &bv,
    const mp_integer &factor,
    const exprt &index);
  NODISCARD
  bvt offset_arithmetic(
    const pointer_typet &type,
    const bvt &bv,
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

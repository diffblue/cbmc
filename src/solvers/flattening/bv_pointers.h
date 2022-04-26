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

  void finish_eager_conversion() override;

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

    postponedt(bvt _bv, bvt _op, exprt _expr)
      : bv(std::move(_bv)), op(std::move(_op)), expr(std::move(_expr))
    {
    }
  };

  typedef std::list<postponedt> postponed_listt;
  postponed_listt postponed_list;

  void do_postponed(const postponedt &postponed);

  /// Given a pointer encoded in \p bv, extract the literals identifying the
  /// object that the pointer points to.
  /// \param bv: Encoded pointer
  /// \param type: Type of the encoded pointer
  /// \return Vector of literals identifying the object part of \p bv
  bvt object_literals(const bvt &bv, const pointer_typet &type) const;

  /// Given a pointer encoded in \p bv, extract the literals representing the
  /// offset into an object that the pointer points to.
  /// \param bv: Encoded pointer
  /// \param type: Type of the encoded pointer
  /// \return Vector of literals identifying the offset part of \p bv
  bvt offset_literals(const bvt &bv, const pointer_typet &type) const;

  /// Construct a pointer encoding from given encodings of \p object and \p
  /// offset.
  /// \param object: Encoded object
  /// \param offset: Encoded offset
  /// \return Pointer encoding
  static bvt object_offset_encoding(const bvt &object, const bvt &offset);
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_BV_POINTERS_WIDE_H
#define CPROVER_CPROVER_BV_POINTERS_WIDE_H

#include <util/nodiscard.h>
#include <util/pointer_expr.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/flattening/pointer_logic.h>

#include "endianness_map_wide.h"

class bv_pointers_widet : public boolbvt
{
public:
  bv_pointers_widet(
    const namespacet &,
    propt &,
    message_handlert &,
    bool get_array_constraints = false);

  void finish_eager_conversion() override;

  std::size_t boolbv_width(const typet &type) const override
  {
    if(type.id() == ID_pointer)
      return 2 * to_pointer_type(type).get_width();
    else
      return boolbvt::boolbv_width(type);
  }

  endianness_mapt
  endianness_map(const typet &type, bool little_endian) const override
  {
    return endianness_map_widet{type, little_endian, ns};
  }

protected:
  pointer_logict pointer_logic;

  std::size_t get_object_width(const pointer_typet &) const;
  std::size_t get_offset_width(const pointer_typet &) const;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef boolbvt SUB;

  NODISCARD
  bvt encode(const mp_integer &object, const pointer_typet &) const;

  virtual bvt convert_pointer_type(const exprt &);

  NODISCARD
  virtual bvt add_addr(const exprt &);

  // overloading
  literalt convert_rest(const exprt &) override;
  bvt convert_bitvector(const exprt &) override; // no cache

  exprt
  bv_get_rec(const exprt &, const bvt &, std::size_t offset) const override;

  NODISCARD
  optionalt<bvt> convert_address_of_rec(const exprt &);

  NODISCARD
  bvt offset_arithmetic(const pointer_typet &, const bvt &, const mp_integer &);
  NODISCARD
  bvt offset_arithmetic(
    const pointer_typet &,
    const bvt &,
    const mp_integer &factor,
    const exprt &index);
  NODISCARD
  bvt offset_arithmetic(
    const pointer_typet &,
    const bvt &,
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

  /// Table that maps a 'pointer number' to its full-width bit-vector.
  /// Used for conversion of pointers to integers.
  std::vector<bvt> numbered_pointers;
};

#endif // CPROVER_CPROVER_BV_POINTERS_WIDE_H

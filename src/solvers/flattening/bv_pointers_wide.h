/*******************************************************************\

Module:

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Pointer encoding using solver-level maps

#ifndef CPROVER_SOLVERS_FLATTENING_BV_POINTERS_WIDE_H
#define CPROVER_SOLVERS_FLATTENING_BV_POINTERS_WIDE_H

#include "boolbv.h"
#include "pointer_logic.h"

#include <map>
#include <unordered_map>

/// Encodes pointer expressions using solver-level arrays (maps) instead
/// of bit-packing.  Each pointer-typed expression is represented as an
/// integer index (using the full pointer width).  Two global array
/// symbols -- one for the object id and one for the byte offset --
/// map that index to the object number and offset respectively.
class bv_pointers_widet : public boolbvt
{
public:
  bv_pointers_widet(
    const namespacet &,
    propt &,
    message_handlert &,
    bool get_array_constraints = false);

  void finish_eager_conversion() override;

  endianness_mapt
  endianness_map(const typet &, bool little_endian) const override;

protected:
  pointer_logict pointer_logic;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef boolbvt SUB;

  /// Width helpers -- all widths equal the pointer width.
  std::size_t get_object_width(const pointer_typet &) const;
  std::size_t get_offset_width(const pointer_typet &) const;
  std::size_t get_address_width(const pointer_typet &) const;

  // Solver-level array symbols for the object and offset maps.
  symbol_exprt object_map;
  symbol_exprt offset_map;

  /// Solver-level array mapping object numbers to symbolic base addresses.
  /// Used for pointer-to-integer casts: the integer value is
  /// base_address_map[object] + offset.
  symbol_exprt base_address_map;

  /// Cache of base address bitvectors per object number.
  /// Populated lazily when pointer-to-integer casts are encountered.
  std::map<mp_integer, bvt> object_base_address;

  /// Objects created from integer-to-pointer casts of constants.
  /// These are excluded from non-overlapping constraints because
  /// the integer address might point into an existing object.
  std::set<mp_integer> integer_address_objects;

  /// Counter for allocating fresh pointer indices.
  mp_integer next_bv_pointer_index;

  /// Map from pointer index to (object, offset) for model
  /// extraction in bv_get_rec.  Populated by encode().
  std::map<mp_integer, std::pair<mp_integer, mp_integer>>
    index_to_object_offset;

  /// Map from pointer index to (object_bv, offset_bv) for model
  /// extraction of encode_fresh pointers.
  std::map<mp_integer, std::pair<bvt, bvt>> index_to_bv_object_offset;

  /// Allocate a fresh index bitvector, constrain the maps, and return
  /// the index as a bvt.
  [[nodiscard]] bvt encode(const mp_integer &object, const pointer_typet &);

  /// Like encode but for a fresh symbolic pointer index.
  [[nodiscard]] bvt encode_fresh(
    const bvt &object_bv,
    const bvt &offset_bv,
    const pointer_typet &type);

  virtual bvt convert_pointer_type(const exprt &);

  [[nodiscard]] virtual bvt add_addr(const exprt &);

  // overloading
  literalt convert_rest(const exprt &) override;
  bvt convert_bitvector(const exprt &) override;

  exprt
  bv_get_rec(const exprt &, const bvt &, std::size_t offset) const override;

  [[nodiscard]] std::optional<bvt> convert_address_of_rec(const exprt &);

  [[nodiscard]] bvt
  offset_arithmetic(const pointer_typet &, const bvt &, const mp_integer &);
  [[nodiscard]] bvt offset_arithmetic(
    const pointer_typet &,
    const bvt &,
    const mp_integer &factor,
    const exprt &index);
  [[nodiscard]] bvt offset_arithmetic(
    const pointer_typet &type,
    const bvt &bv,
    const exprt &factor,
    const exprt &index);
  [[nodiscard]] bvt offset_arithmetic(
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

  /// Build a constant expression from a pointer index.
  exprt index_to_expr(const mp_integer &index, const pointer_typet &type) const;

  /// Read the object number for a pointer whose bitvector is \p bv.
  bvt read_object(const bvt &bv, const pointer_typet &type);

  /// Read the offset for a pointer whose bitvector is \p bv.
  bvt read_offset(const bvt &bv, const pointer_typet &type);

  /// Get or create a symbolic base address bitvector for the given
  /// object number. Used for pointer-to-integer casts.
  bvt get_object_base_address(const mp_integer &object, std::size_t width);

  /// Create Boolean functions describing all dynamic and all
  /// not-dynamic object encodings over \p placeholders as input
  /// Boolean variables representing object bits.
  std::pair<exprt, exprt> prepare_postponed_is_dynamic_object(
    std::vector<symbol_exprt> &placeholders) const;

  /// Create Boolean functions describing all objects of each
  /// known object size over \p placeholders as input Boolean
  /// variables representing object bits.
  std::unordered_map<exprt, exprt, irep_hash>
  prepare_postponed_object_size(std::vector<symbol_exprt> &placeholders) const;
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_POINTERS_WIDE_H

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H
#define CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H

#include "boolbv.h"
#include "pointer_logic.h"

#include <optional>

class byte_extract_exprt;
class byte_update_exprt;

class bv_pointerst:public boolbvt
{
public:
  bv_pointerst(
    const namespacet &,
    propt &,
    message_handlert &,
    bool get_array_constraints = false);

  void finish_eager_conversion() override;
  bool boolbv_set_equality_to_true(const equal_exprt &expr) override;
  decision_proceduret::resultt dec_solve(const exprt &) override;

  /// Check backward I2P constraints against the current SAT model.
  /// Returns true if any constraints were added (progress made).
  /// Used by both bv_pointerst::dec_solve and bv_refinementt::check_SAT.
  bool check_SAT_backward_i2p();

  endianness_mapt
  endianness_map(const typet &, bool little_endian) const override;

  /// Enable (or disable) the wide pointer encoding that includes a flat
  /// integer address alongside the object/offset.  This fixes pointer-to-
  /// integer casts, integer-to-pointer casts, and byte-level operations on
  /// pointer-containing types.  The pointer width tracked by bv_width is kept
  /// in sync, so this is the single switch that turns the feature on.
  void set_wide_pointer_encoding(bool enabled)
  {
    wide_pointer_encoding = enabled;
    bv_width.set_wide_pointer_encoding(enabled);
  }

protected:
  /// Whether the wide pointer encoding is in use; flip via
  /// set_wide_pointer_encoding(), which keeps bv_width in sync.
  bool wide_pointer_encoding = false;

  pointer_logict pointer_logic;

  /// Layout: [object | offset | address]
  /// When wide_pointer_encoding is false, address_width is 0
  /// and the layout is the traditional [offset | object].
  std::size_t get_object_width(const pointer_typet &) const;
  std::size_t get_offset_width(const pointer_typet &) const;
  std::size_t get_address_width(const pointer_typet &) const;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef boolbvt SUB;

  [[nodiscard]] bvt
  encode(const mp_integer &object, const pointer_typet &) const;

  virtual bvt convert_pointer_type(const exprt &);

  /// Reconstruct a wide pointer encoding (object|offset|address) from a flat
  /// address, which may arise, e.g., from an integer-to-pointer cast or a
  /// byte-level read).
  /// \param addr_bv: flat address (non-pointer-type bitvector)
  /// \param ptr_type: target pointer type
  /// \param force_base_for_all_objects: if true (integer-to-pointer cast, where
  ///   the address may denote any object) a base address is created for every
  ///   object; if false (byte-extract reconstruction) only objects that
  ///   already have a base address are related.
  [[nodiscard]] bvt reconstruct_pointer_from_address(
    const bvt &addr_bv,
    const pointer_typet &ptr_type,
    bool force_base_for_all_objects);

  [[nodiscard]] virtual bvt add_addr(const exprt &);

  // overloading
  literalt convert_equality(const equal_exprt &) override;
  literalt convert_rest(const exprt &) override;
  bvt convert_bitvector(const exprt &) override; // no cache
  bvt convert_byte_extract(const byte_extract_exprt &expr) override;
  bvt convert_byte_update(const byte_update_exprt &expr) override;

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

  /// Pending integer-to-pointer casts whose backward constraints
  /// are deferred to finish_eager_conversion (when all objects are known).
  struct pending_i2pt
  {
    bvt obj_bv, off_bv, addr_bv;
    std::size_t objects_at_creation;
    bool needs_backward_constraints;
    /// Cache of the per-object equality literals `obj_bv == object number`,
    /// indexed by object number. The same literal is needed by the forward,
    /// validity and backward constraints, so it is built once via
    /// i2p_object_eq() and shared rather than rebuilding the comparator (and
    /// emitting duplicate clauses) in each loop.
    std::vector<std::optional<literalt>> object_eq;
  };
  std::vector<pending_i2pt> pending_i2p;
  unsigned finish_eager_var_start = 0;

  /// Returns the literal that is true iff the pending integer-to-pointer cast
  /// \p p reconstructs to object \p number, building and caching it on first
  /// use (see pending_i2pt::object_eq).
  literalt i2p_object_eq(pending_i2pt &p, std::size_t number);

  typedef std::list<postponedt> postponed_listt;
  postponed_listt postponed_list;

  /// Create Boolean functions describing all dynamic and all not-dynamic object
  /// encodings over \p placeholders as input Boolean variables representing
  /// object bits.
  std::pair<exprt, exprt> prepare_postponed_is_dynamic_object(
    std::vector<symbol_exprt> &placeholders) const;

  /// Create Boolean functions describing all objects of each known object size
  /// over \p placeholders as input Boolean variables representing object bits.
  std::unordered_map<exprt, exprt, irep_hash>
  prepare_postponed_object_size(std::vector<symbol_exprt> &placeholders) const;

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

  /// Given a pointer encoded in \p bv, extract the address literals.
  /// Only meaningful when wide_pointer_encoding is true.
  bvt address_literals(const bvt &bv, const pointer_typet &type) const;

  /// Symbolic base addresses per object number.
  /// Used for wide pointer encoding to compute flat addresses.
  mutable std::map<mp_integer, bvt> object_base_address;
  std::set<mp_integer> integer_address_objects;

  /// Get or create a symbolic base address for an object.
  bvt get_object_base_address(const mp_integer &object, std::size_t width)
    const;

  /// Construct a pointer encoding from given encodings of \p object and \p
  /// offset.
  /// \param object: Encoded object
  /// \param offset: Encoded offset
  /// \return Pointer encoding
  static bvt object_offset_encoding(const bvt &object, const bvt &offset);
  static bvt object_offset_encoding(
    const bvt &object,
    const bvt &offset,
    const bvt &address);
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_POINTERS_H

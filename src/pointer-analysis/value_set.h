/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_H

#include <set>
#include <type_traits>
#include <unordered_set>

#include <util/mp_arith.h>
#include <util/reference_counting.h>
#include <util/sharing_map.h>

#include "object_numbering.h"
#include "value_sets.h"

class namespacet;

/// State type in value_set_domaint, used in value-set analysis and goto-symex.
/// Represents a mapping from expressions to the addresses that may be stored
/// there; for example, a global that is either null or points to a
/// heap-allocated object, which itself has two fields, one pointing to another
/// heap object and the other having unknown target, would be represented:
///
///     global_x -> { null, <dynamic_object1, 0> }
///     dynamic_object1.field1 -> { <dynamic_object2, 0> }
///     dynamic_object1.field2 -> { * (unknown) }
///
/// LHS expressions can be either symbols or fields thereof, and are stored as
/// strings; RHS expressions may be symbols, dynamic objects, integer addresses
/// (as in `(int*)0x1234`) or unknown (printed as `*`), and are stored as
/// pairs of an `exprt` and an optional offset if known (0 for both dynamic
/// objects in the example given above). RHS expressions are represented using
/// numbering to avoid storing redundant duplicate expressions.
class value_sett
{
public:
  value_sett():location_number(0)
  {
  }

  value_sett(value_sett &&other)
    : location_number(other.location_number), values(std::move(other.values))
  {
  }

  virtual ~value_sett() = default;

  value_sett(const value_sett &other) = default;

  value_sett &operator=(const value_sett &other) = delete;

  value_sett &operator=(value_sett &&other)
  {
    values = std::move(other.values);
    return *this;
  }

  /// Determines whether an identifier of a given type should have its fields
  /// distinguished. Virtual so that subclasses can override this behaviour.
  virtual bool field_sensitive(const irep_idt &id, const typet &type);

  /// Matches the location_number field of the instruction that corresponds
  /// to this value_sett instance in value_set_domaint's state map
  unsigned location_number;

  /// Global shared object numbering, used to abbreviate expressions stored
  /// in value sets.
  static object_numberingt object_numbering;

  /// Represents the offset into an object: either a unique integer offset,
  /// or an unknown value, represented by `!offset`.
  typedef optionalt<mp_integer> offsett;
  DEPRECATED(SINCE(2019, 05, 22, "Unused"))
  bool offset_is_zero(const offsett &offset) const
  {
    return offset && offset->is_zero();
  }

  /// Represents a set of expressions (`exprt` instances) with corresponding
  /// offsets (`offsett` instances). This is the RHS set of a single row of
  /// the enclosing `value_sett`, such as `{ null, dynamic_object1 }`.
  /// The set is represented as a map from numbered `exprt`s to `offsett`
  /// instead of a set of pairs to make lookup by `exprt` easier.
  using object_map_dt = std::map<object_numberingt::number_type, offsett>;

  static const object_map_dt empty_object_map;

  /// Converts an `object_map_dt` element `object_number -> offset` into an
  /// `object_descriptor_exprt` with
  /// `.object() == object_numbering.at(object_number)` and
  /// `.offset() == offset`.
  exprt to_expr(const object_map_dt::value_type &it) const;

  /// Reference-counts instances of `object_map_dt`, such that multiple
  /// instructions' `value_sett` instances can share them. For example, if
  /// we have a pair of instructions with value-sets:
  ///
  ///     x = new A;
  ///       x -> { dynamic_object1 }
  ///     y = new B;
  ///       x -> { dynamic_object1 }
  ///       y -> { dynamic_object2 }
  ///
  /// Then the set { dynamic_object1 }, represented by an `object_map_dt`, can
  /// be shared between the two `value_sett` instances.
  using object_mapt = reference_counting<object_map_dt, empty_object_map>;

  /// Sets an element in object map `dest` to match an existing element `it`
  /// from a different map. Any existing element for the same `exprt` is
  /// overwritten.
  /// \param dest: object map to update.
  /// \param it: iterator pointing to new element
  void set(object_mapt &dest, const object_map_dt::value_type &it) const
  {
    dest.write()[it.first]=it.second;
  }

  /// Merges an existing element into an object map. If the destination map
  /// has an existing element for the same expression with a different offset
  /// its offset is marked unknown (so e.g. `x -> 0` and `x -> 1` merge into
  /// `x -> ?`).
  /// \param dest: object map to update.
  /// \param it: iterator pointing to new element
  bool insert(object_mapt &dest, const object_map_dt::value_type &it) const
  {
    return insert(dest, it.first, it.second);
  }

  /// Adds an expression to an object map, with unknown offset. If the
  /// destination map has an existing element for the same expression
  /// its offset is marked unknown.
  /// \param dest: object map to update
  /// \param src: expression to add
  bool insert(object_mapt &dest, const exprt &src) const
  {
    return insert(dest, object_numbering.number(src), offsett());
  }

  /// Adds an expression to an object map, with known offset. If the
  /// destination map has an existing element for the same expression
  /// with a differing offset its offset is marked unknown.
  /// \param dest: object map to update
  /// \param src: expression to add
  /// \param offset_value: offset into `src`
  bool insert(
    object_mapt &dest,
    const exprt &src,
    const mp_integer &offset_value) const
  {
    return insert(dest, object_numbering.number(src), offsett(offset_value));
  }

  /// Adds a numbered expression and offset to an object map. If the
  /// destination map has an existing element for the same expression
  /// with a differing offset its offset is marked unknown.
  /// \param dest: object map to update
  /// \param n: object number to add; must be mapped to the corresponding
  ///   expression by `object_numbering`.
  /// \param offset: offset into object `n` (may be unknown).
  bool insert(
    object_mapt &dest,
    object_numberingt::number_type n,
    const offsett &offset) const;

  enum class insert_actiont
  {
    INSERT,
    RESET_OFFSET,
    NONE
  };

  /// Determines what would happen if object number \p n was inserted into map
  /// \p dest with offset \p offset -- the possibilities being, nothing (the
  /// entry is already present), a new entry would be inserted (no existing
  /// entry with number \p n was found), or an existing entry's offset would be
  /// reset (indicating there is already an entry with number \p n, but with
  /// differing offset).
  insert_actiont get_insert_action(
    const object_mapt &dest,
    object_numberingt::number_type n,
    const offsett &offset) const;

  /// Adds an expression and offset to an object map. If the
  /// destination map has an existing element for the same expression
  /// with a differing offset its offset is marked unknown.
  /// \param dest: object map to update
  /// \param expr: expression to add
  /// \param offset: offset into `expr` (may be unknown).
  bool insert(object_mapt &dest, const exprt &expr, const offsett &offset) const
  {
    return insert(dest, object_numbering.number(expr), offset);
  }

  /// Represents a row of a `value_sett`. For example, this might represent
  /// `dynamic_object1.field1 -> { <dynamic_object2, 0> }`, with
  /// `identifier == dynamic_object1`, `suffix` == `.field1` and
  /// a single-element `object_map` representing `{ <dynamic_object2, 0> }`.
  struct entryt
  {
    object_mapt object_map;
    irep_idt identifier;
    std::string suffix;

    entryt()
    {
    }

    entryt(const irep_idt &_identifier, const std::string &_suffix)
      : identifier(_identifier), suffix(_suffix)
    {
    }

    bool operator==(const entryt &other) const
    {
      // Note that the object_map comparison below is duplicating the code of
      // operator== defined in reference_counting.h because old versions of
      // clang (3.7 and 3.8) do not resolve the template instantiation correctly
      return identifier == other.identifier && suffix == other.suffix &&
             (object_map.get_d() == other.object_map.get_d() ||
              object_map.read() == other.object_map.read());
    }
    bool operator!=(const entryt &other) const
    {
      return !(*this==other);
    }
  };

  /// Set of expressions; only used for the `get` API, not for internal
  /// data representation.
  DEPRECATED(SINCE(2019, 05, 22, "Only used in deprecated function"))
  typedef std::set<exprt> expr_sett;

  /// Set of dynamic object numbers, equivalent to a set of
  /// `dynamic_object_exprt`s with corresponding IDs. Used only in internal
  /// implementation details.
  DEPRECATED(SINCE(2019, 05, 22, "Unused"))
  typedef std::set<unsigned int> dynamic_object_id_sett;

  /// Map representing the entire value set, mapping from string LHS IDs
  /// to RHS expression sets. Note this data structure is somewhat
  /// denormalized, for example mapping
  ///
  ///     dynamic_object1.field2 ->
  ///         entryt {
  ///          .identifier = dynamic_object1,
  ///          .suffix = .field2,
  ///          .object_map = ...
  ///         }
  ///
  /// The components of the ID are thus duplicated in the `valuest` key and in
  /// `entryt` fields.
  typedef sharing_mapt<irep_idt, entryt> valuest;

  /// Gets values pointed to by \p expr, including following dereference
  /// operators (i.e. this is not a simple lookup in `valuest`).
  DEPRECATED(
    SINCE(2019, 05, 22, "Use get_value_set(exprt, const namespacet &) instead"))
  void get_value_set(
    exprt expr,
    value_setst::valuest &dest,
    const namespacet &ns) const;

  /// Gets values pointed to by `expr`, including following dereference
  /// operators (i.e. this is not a simple lookup in `valuest`).
  /// \param expr: query expression
  /// \param ns: global namespace
  /// \return list of expressions that `expr` may point to. These expressions
  ///   are object_descriptor_exprt or have id ID_invalid or ID_unknown.
  std::vector<exprt> get_value_set(exprt expr, const namespacet &ns) const;

  /// Appears to be unimplemented.
  DEPRECATED(SINCE(2019, 05, 22, "Unimplemented"))
  expr_sett &get(const irep_idt &identifier, const std::string &suffix);

  void clear()
  {
    values.clear();
  }

  /// Finds an entry in this value-set. The interface differs from
  /// \ref update_entry because get_value_set_rec wants to check for a struct's
  /// first component before stripping the suffix as is done in
  /// \ref update_entry.
  /// \param id: identifier to find.
  /// \return a constant pointer to an entry if found, or null otherwise.
  const entryt *find_entry(const irep_idt &id) const;

  /// Adds or replaces an entry in this value-set.
  /// \param e: entry to find. Its `id` and `suffix` fields will be used
  ///   to find a corresponding entry; if a fresh entry is created its
  ///   `object_map` (RHS value set) will be merged with or replaced by \p
  ///   new_values, depending on the value of \p add_to_sets. If an entry
  ///   already exists, the object map of \p e is ignored.
  /// \param type: type of `e.identifier`, used to determine whether `e`'s
  ///   suffix should be used to find a field-sensitive value-set or whether
  ///   a single entry should be shared by all of symbol `e.identifier`.
  /// \param new_values: values to be stored for the entry.
  /// \param add_to_sets: if true, merge in \p new_values instead of replacing
  ///   the existing values.
  void update_entry(
    const entryt &e,
    const typet &type,
    const object_mapt &new_values,
    bool add_to_sets);

  /// Pretty-print this value-set
  /// \param [out] out: stream to write to
  /// \param indent: string to use for indentation of the output
  void output(std::ostream &out, const std::string &indent = "") const;

  DEPRECATED(SINCE(2019, 06, 11, "Use the version without ns argument"))
  void output(
    const namespacet &ns,
    std::ostream &out,
    const std::string &indent = "") const;

  /// Stores the LHS ID -> RHS expression set map. See `valuest` documentation
  /// for more detail.
  valuest values;

  /// Merges two RHS expression sets
  /// \param [in, out] dest: set to merge into
  /// \param src: set to merge in
  /// \return true if anything changed.
  bool make_union(object_mapt &dest, const object_mapt &src) const;

  /// Determines whether merging two RHS expression sets would cause any change
  /// \param dest: set that would be merged into
  /// \param src: set that would be merged in
  /// \return true if anything changed.
  bool make_union_would_change(const object_mapt &dest, const object_mapt &src)
    const;

  /// Merges an entire existing value_sett's data into this one
  /// \param new_values: new values to merge in
  /// \return true if anything changed.
  bool make_union(const valuest &new_values);

  /// Merges an entire existing value_sett's data into this one
  /// \return true if anything changed.
  bool make_union(const value_sett &new_values)
  {
    return make_union(new_values.values);
  }

  /// Transforms this value-set by assuming an expression holds.
  /// Currently this can only mark dynamic objects valid; all other
  /// assumptions are ignored.
  /// \param expr: condition to assume
  /// \param ns: global namespace
  void guard(
    const exprt &expr,
    const namespacet &ns);

  /// Transforms this value-set by executing a given statement against it.
  /// For example, assignment statements will update `valuest` by reading
  /// the value-set corresponding to their right-hand side and assigning it
  /// to their LHS.
  /// \param code: instruction to apply
  /// \param ns: global namespace
  void apply_code(
    const codet &code,
    const namespacet &ns)
  {
    apply_code_rec(code, ns);
  }

  /// Transforms this value-set by executing executing the assignment
  /// `lhs := rhs` against it.
  /// \param lhs: written expression
  /// \param rhs: read expression
  /// \param ns: global namespace
  /// \param is_simplified: if false, `simplify` will be used to simplify
  ///   RHS and LHS before execution. If you know they are already simplified,
  ///   set this to save a little time.
  /// \param add_to_sets: if true, execute a weak assignment (the LHS possible
  ///   values are added to but not overwritten). Otherwise execute a strong
  ///   (overwriting) assignment. Note the nature of `lhs` may internally
  ///   prevent a strong assignment, as in `x == y ? z : w := a`, where either
  ///   `y` or `z` MAY, but not MUST, be overwritten.
  void assign(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns,
    bool is_simplified,
    bool add_to_sets);

  /// Transforms this value-set by executing the actual -> formal parameter
  /// assignments for a particular callee. For example, for function
  /// `f(int* x, void* y)` and call `f(&g, &h)` this would execute assignments
  /// `x := &g` and `y := &h`.
  /// \param function: function being called
  /// \param arguments: actual arguments
  /// \param ns: global namespace
  void do_function_call(
    const irep_idt &function,
    const exprt::operandst &arguments,
    const namespacet &ns);

  /// Transforms this value-set by assigning this function's return value to
  /// a given LHS expression. Note this has no effect if `remove_returns` has
  /// been run, in which case returns are explicitly passed via global
  /// variables named `function_name#return_value` and are handled via the usual
  /// `apply_code` path.
  /// \param lhs: expression that receives the return value
  /// \param ns: global namespace
  void do_end_function(
    const exprt &lhs,
    const namespacet &ns);

  /// Gets the set of expressions that `expr` may refer to, according to this
  /// value set. Note the contrast with `get_value_set`: if `x` holds a pointer
  /// to `y`, then `get_value_set(x)` includes `y` while `get_reference_set(x)`
  /// returns `{ x }`.
  /// \param expr: query expression
  /// \param [out] dest: overwritten with result expression set
  /// \param ns: global namespace
  void get_reference_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns) const;

  /// Tries to resolve any `pointer_offset_exprt` expressions in `expr` to
  /// constant integers using this value-set's information. For example, if
  /// `expr` contained `POINTER_OFFSET(y)`, and this value set indicates `y`
  /// points to object `z` offset `4`, then the expression will be replaced by
  /// constant `4`. If we don't know where `y` points, or it may point to
  /// multiple distinct offsets, then the expression will be left alone.
  /// \param expr: expression whose pointer offsets should be replaced
  /// \param ns: global namespace
  /// \return true if any offset expression was successfully replaced.
  bool eval_pointer_offset(
    exprt &expr,
    const namespacet &ns) const;

  /// Get the index of the symbol and suffix
  /// \param identifier: The identifier for the symbol
  /// \param type: The type of the symbol
  /// \param suffix: The suffix for the entry
  /// \param ns: The global namespace, for following \p type if it is a
  ///   struct tag type or a union tag type
  /// \return The index if the symbol is known, else `nullopt`.
  optionalt<irep_idt> get_index_of_symbol(
    irep_idt identifier,
    const typet &type,
    const std::string &suffix,
    const namespacet &ns) const;

  /// Update the entry stored at \p index by erasing any values listed in
  /// \p values_to_erase.
  /// \param index: index in the value set
  /// \param values_to_erase: set of values to remove from the entry
  void erase_values_from_entry(
    const irep_idt &index,
    const std::unordered_set<exprt, irep_hash> &values_to_erase);

  void erase_symbol(const symbol_exprt &symbol_expr, const namespacet &ns);

protected:
  /// Reads the set of objects pointed to by \p expr, including making
  /// recursive lookups for dereference operations etc.
  DEPRECATED(
    SINCE(2019, 05, 22, "Use the version returning object_mapt instead"))
  void get_value_set(
    exprt expr,
    object_mapt &dest,
    const namespacet &ns,
    bool is_simplified) const;

  /// Reads the set of objects pointed to by `expr`, including making
  /// recursive lookups for dereference operations etc.
  /// \param expr: query expression
  /// \param ns: global namespace
  /// \param is_simplified: if false, simplify `expr` before reading.
  /// \return the set of object numbers pointed to
  object_mapt
  get_value_set(exprt expr, const namespacet &ns, bool is_simplified) const;

  /// See the other overload of `get_reference_set`. This one returns object
  /// numbers and offsets instead of expressions.
  void get_reference_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const
  {
    get_reference_set_rec(expr, dest, ns);
  }

  /// See get_reference_set.
  void get_reference_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const;

  /// Sets `dest` to `src` with any wrapping typecasts removed
  void dereference_rec(
    const exprt &src,
    exprt &dest) const;

  void erase_symbol_rec(
    const typet &type,
    const std::string &erase_prefix,
    const namespacet &ns);

  void erase_struct_union_symbol(
    const struct_union_typet &struct_union_type,
    const std::string &erase_prefix,
    const namespacet &ns);

  // Subclass customisation points:

protected:
  /// Subclass customisation point for recursion over RHS expression:
  virtual void get_value_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const std::string &suffix,
    const typet &original_type,
    const namespacet &ns) const;

  /// Subclass customisation point for recursion over LHS expression:
  virtual void assign_rec(
    const exprt &lhs,
    const object_mapt &values_rhs,
    const std::string &suffix,
    const namespacet &ns,
    bool add_to_sets);

  /// Subclass customisation point for applying code to this domain:
  virtual void apply_code_rec(
    const codet &code,
    const namespacet &ns);

 private:
  /// Subclass customisation point to filter or otherwise alter the value-set
  /// returned from get_value_set before it is passed into assign. For example,
  /// this is used in one subclass to tag and thus differentiate values that
  /// originated in a particular place, vs. those that have been copied.
  virtual void adjust_assign_rhs_values(
    const exprt &rhs,
    const namespacet &,
    object_mapt &rhs_values) const
  {
    // unused parameters
    (void)rhs;
    (void)rhs_values;
  }

  /// Subclass customisation point to apply global side-effects to this domain,
  /// after RHS values are read but before they are written. For example, this
  /// is used in a recency-analysis plugin to demote existing most-recent
  /// objects to general case ones.
  virtual void apply_assign_side_effects(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &)
  {
    // unused parameters
    (void)lhs;
    (void)rhs;
  }
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_H

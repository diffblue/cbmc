/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_H

#include <set>

#include <util/mp_arith.h>
#include <util/reference_counting.h>

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

  virtual ~value_sett() = default;

  static bool field_sensitive(
    const irep_idt &id,
    const typet &type,
    const namespacet &);

  /// Matches the location_number field of the instruction that corresponds
  /// to this value_sett instance in value_set_domaint's state map
  unsigned location_number;

  /// Global shared object numbering, used to abbreviate expressions stored
  /// in value sets.
  static object_numberingt object_numbering;

  typedef irep_idt idt;

  /// Represents the offset into an object: either a unique integer offset,
  /// or an unknown value, represented by `!offset`.
  typedef optionalt<mp_integer> offsett;
  bool offset_is_zero(const offsett &offset) const
  {
    return offset && offset->is_zero();
  }

  /// Represents a set of expressions (`exprt` instances) with corresponding
  /// offsets (`offsett` instances). This is the RHS set of a single row of
  /// the enclosing `value_sett`, such as `{ null, dynamic_object1 }`.
  /// The set is represented as a map from numbered `exprt`s to `offsett`
  /// instead of a set of pairs to make lookup by `exprt` easier. All
  /// methods matching the interface of `std::map` forward those methods
  /// to the internal map.
  class object_map_dt
  {
    typedef std::map<object_numberingt::number_type, offsett> data_typet;
    data_typet data;

  public:
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::iterator iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::const_iterator const_iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::value_type value_type;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::key_type key_type;

    iterator begin() { return data.begin(); }
    const_iterator begin() const { return data.begin(); }
    const_iterator cbegin() const { return data.cbegin(); }

    iterator end() { return data.end(); }
    const_iterator end() const { return data.end(); }
    const_iterator cend() const { return data.cend(); }

    size_t size() const { return data.size(); }
    bool empty() const { return data.empty(); }

    void erase(key_type i) { data.erase(i); }
    void erase(const_iterator it) { data.erase(it); }

    offsett &operator[](key_type i)
    {
      return data[i];
    }
    offsett &at(key_type i)
    {
      return data.at(i);
    }
    const offsett &at(key_type i) const
    {
      return data.at(i);
    }

    template <typename It>
    void insert(It b, It e) { data.insert(b, e); }

    template <typename T>
    const_iterator find(T &&t) const { return data.find(std::forward<T>(t)); }

    static const object_map_dt blank;

    object_map_dt()=default;

    bool operator==(const object_map_dt &other) const
    {
      return data==other.data;
    }
    bool operator!=(const object_map_dt &other) const
    {
      return !(*this==other);
    }

  protected:
    ~object_map_dt()=default;
  };

  /// Converts an `object_map_dt` entry `object_number -> offset` into an
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
  typedef reference_counting<object_map_dt> object_mapt;

  /// Sets an entry in object map `dest` to match an existing entry `it`
  /// from a different map. Any existing entry for the same `exprt` is
  /// overwritten.
  /// \param dest: object map to update.
  /// \param it: iterator pointing to new entry
  void set(object_mapt &dest, const object_map_dt::value_type &it) const
  {
    dest.write()[it.first]=it.second;
  }

  /// Merges an existing entry into an object map. If the destination map
  /// has an existing entry for the same expression with a different offset
  /// its offset is marked unknown (so e.g. `x -> 0` and `x -> 1` merge into
  /// `x -> ?`).
  /// \param dest: object map to update.
  /// \param it: iterator pointing to new entry
  bool insert(object_mapt &dest, const object_map_dt::value_type &it) const
  {
    return insert(dest, it.first, it.second);
  }

  /// Adds an expression to an object map, with unknown offset. If the
  /// destination map has an existing entry for the same expression
  /// its offset is marked unknown.
  /// \param dest: object map to update
  /// \param src: expression to add
  bool insert(object_mapt &dest, const exprt &src) const
  {
    return insert(dest, object_numbering.number(src), offsett());
  }

  /// Adds an expression to an object map, with known offset. If the
  /// destination map has an existing entry for the same expression
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
  /// destination map has an existing entry for the same expression
  /// with a differing offset its offset is marked unknown.
  /// \param dest: object map to update
  /// \param n: object number to add; must be mapped to the corresponding
  ///   expression by `object_numbering`.
  /// \param offset: offset into object `n` (may be unknown).
  bool insert(
    object_mapt &dest,
    object_numberingt::number_type n,
    const offsett &offset) const;

  /// Adds an expression and offset to an object map. If the
  /// destination map has an existing entry for the same expression
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
  /// a single-entry `object_map` representing `{ <dynamic_object2, 0> }`.
  struct entryt
  {
    object_mapt object_map;
    idt identifier;
    std::string suffix;

    entryt()
    {
    }

    entryt(const idt &_identifier, const std::string &_suffix):
      identifier(_identifier),
      suffix(_suffix)
    {
    }

    bool operator==(const entryt &other) const
    {
      return
        identifier==other.identifier &&
        suffix==other.suffix &&
        object_map==other.object_map;
    }
    bool operator!=(const entryt &other) const
    {
      return !(*this==other);
    }
  };

  /// Set of expressions; only used for the `get` API, not for internal
  /// data representation.
  typedef std::set<exprt> expr_sett;

  /// Set of dynamic object numbers, equivalent to a set of
  /// `dynamic_object_exprt`s with corresponding IDs. Used only in internal
  /// implementation details.
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
  #ifdef USE_DSTRING
  typedef std::map<idt, entryt> valuest;
  #else
  typedef std::unordered_map<idt, entryt, string_hash> valuest;
  #endif

  /// Gets values pointed to by `expr`, including following dereference
  /// operators (i.e. this is not a simple lookup in `valuest`).
  /// \param expr: query expression
  /// \param [out] dest: assigned a set of expressions that `expr` may point to
  /// \param ns: global namespace
  void get_value_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns) const;

  /// Appears to be unimplemented.
  expr_sett &get(
    const idt &identifier,
    const std::string &suffix);

  /// Clears value set (not used in the CBMC repository)
  void make_any()
  {
    values.clear();
  }

  void clear()
  {
    values.clear();
  }

  /// Gets or inserts an entry in this value-set.
  /// \param e: entry to find. Its `id` and `suffix` fields will be used
  ///   to find a corresponding entry; if a fresh entry is created its
  ///   `object_map` (RHS value set) will be copied; otherwise it will be
  ///   ignored. Therefore it should probably be left blank and any RHS updates
  ///   conducted against the returned reference.
  /// \param type: type of `e.identifier`, used to determine whether `e`'s
  ///   suffix should be used to find a field-sensitive value-set or whether
  ///   a single entry should be shared by all of symbol `e.identifier`.
  /// \param ns: global namespace
  entryt &get_entry(
    const entryt &e, const typet &type,
    const namespacet &ns);

  /// Pretty-print this value-set
  /// \param ns: global namespace
  /// \param [out] out: stream to write to
  void output(
    const namespacet &ns,
    std::ostream &out) const;

  /// Stores the LHS ID -> RHS expression set map. See `valuest` documentation
  /// for more detail.
  valuest values;

  /// Merges two RHS expression sets
  /// \param [in, out] dest: set to merge into
  /// \param src: set to merge in
  /// \return true if anything changed.
  bool make_union(object_mapt &dest, const object_mapt &src) const;

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

protected:
  /// Reads the set of objects pointed to by `expr`, including making
  /// recursive lookups for dereference operations etc.
  /// \param expr: query expression
  /// \param dest [out]: overwritten by the set of object numbers pointed to
  /// \param ns; global namespace
  /// \param is_simplified: if false, simplify `expr` before reading.
  void get_value_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns,
    bool is_simplified) const;

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

  /// Extracts a member from a struct- or union-typed expression.
  /// Usually that means making a `member_exprt`, but this can shortcut
  /// extracting members from constants or with-expressions.
  /// \param src: base struct-or-union-typed expression
  /// \param component_name: member to extract
  /// \param ns: global namespace
  exprt make_member(
    const exprt &src,
    const irep_idt &component_name,
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
  }
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_H

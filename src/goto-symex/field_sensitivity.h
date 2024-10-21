/*******************************************************************\

Module: Field-sensitive SSA

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H
#define CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H

#include <util/ssa_expr.h>

#define ENABLE_ARRAY_FIELD_SENSITIVITY

class namespacet;
class goto_symex_statet;
class symex_targett;

class field_sensitive_ssa_exprt : public exprt
{
public:
  field_sensitive_ssa_exprt(const ssa_exprt &ssa, exprt::operandst &&fields)
    : exprt(ID_field_sensitive_ssa, ssa.type(), std::move(fields))
  {
    add(ID_expression, ssa);
  }

  const ssa_exprt &get_object_ssa() const
  {
    return static_cast<const ssa_exprt &>(find(ID_expression));
  }
};

template <>
inline bool can_cast_expr<field_sensitive_ssa_exprt>(const exprt &base)
{
  return base.id() == ID_field_sensitive_ssa;
}

inline const field_sensitive_ssa_exprt &
to_field_sensitive_ssa_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_field_sensitive_ssa);
  const field_sensitive_ssa_exprt &ret =
    static_cast<const field_sensitive_ssa_exprt &>(expr);
  return ret;
}

inline field_sensitive_ssa_exprt &to_field_sensitive_ssa_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_field_sensitive_ssa);
  field_sensitive_ssa_exprt &ret =
    static_cast<field_sensitive_ssa_exprt &>(expr);
  return ret;
}

/// Control granularity of object accesses
///
/// [Field sensitivity](\ref field_sensitivityt) is a transformation of the
/// instructions goto-program which mainly replaces some expressions by symbols
/// but can also add assignments to the target equations produced by symbolic
/// execution.
/// The main goal of this transformation is to allow more constants to be
/// propagated during symbolic execution.
/// Note that field sensitivity is not applied as a single pass over the
/// whole goto program but instead applied as the symbolic execution unfolds.
///
/// On a high level, field sensitivity replaces member operators, and array
/// accesses with atomic symbols representing a field when possible.
/// In cases where this is not immediately possible, like struct assignments,
/// some things need to be added.
/// The possible cases are described below.
///
/// ### Member access
/// A member expression `struct_expr.field_name` is replaced by the
/// symbol `struct_expr..field_name`; note the use of `..` to visually
/// distinguish the symbol from the member expression. This is valid for
/// both lvalues and rvalues. See \ref field_sensitivityt::apply.
///
/// ### Symbols representing structs
/// In an rvalue, a symbol struct_expr which has a struct type with fields
/// field1, field2, etc, will be replaced by
/// `{struct_expr..field_name1; struct_expr..field_name2; …}`.
/// See \ref field_sensitivityt::get_fields.
///
/// ### Assignment to a struct
/// When the symbol is on the left-hand-side, for instance for an assignment
/// `struct_expr = other_struct`, the assignment is replaced by a sequence
/// of assignments:
/// `struct_expr..field_name1 = other_struct..field_name1;`
/// `struct_expr..field_name2 = other_struct..field_name2;` etc.
/// See \ref field_sensitivityt::field_assignments.
///
/// ### Array access
/// An index expression `array[index]` when index is constant and array has
/// constant size is replaced by the symbol `array[[index]]`; note the use
/// of `[[` and `]]` to visually distinguish the symbol from the index
/// expression.
/// When `index` is not a constant, `array[index]` is replaced by
///  `{array[[0]]; array[[1]]; …index]`.
/// Note that this process does not apply to arrays whose size is not constant,
/// and arrays whose size exceed the bound \c max_field_sensitivity_array_size.
/// See \ref field_sensitivityt::apply.
///
/// ### Symbols representing arrays
/// In an rvalue, a symbol `array` which has array type will be replaced by
/// `{array[[0]]; array[[1]]; …}[index]`.
/// See \ref field_sensitivityt::get_fields.
///
/// ### Assignment to an array
/// When the array symbol is on the left-hand-side, for instance for
/// an assignment `array = other_array`, the assignment is replaced by a
/// sequence of assignments:
/// `array[[0]] = other_array[[0]]`;
/// `array[[1]] = other_array[[1]]`; etc.
/// See \ref field_sensitivityt::field_assignments.
class field_sensitivityt
{
public:
  /// \param max_array_size: maximum size for which field sensitivity will be
  ///   applied to array cells
  /// \param should_simplify: simplify expressions
  field_sensitivityt(std::size_t max_array_size, bool should_simplify)
    :
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
      max_field_sensitivity_array_size(max_array_size),
#endif
      should_simplify(should_simplify)
  {
  }

  /// Assign to the individual fields of a non-expanded symbol \p lhs. This is
  /// required whenever prior steps have updated the full object rather than
  /// individual fields, e.g., in case of assignments to an array at an unknown
  /// index.
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param state: symbolic execution state
  /// \param lhs: non-expanded symbol
  /// \param rhs: right-hand-side value that was used in the preceding update of
  ///   the full object
  /// \param target: symbolic execution equation store
  /// \param allow_pointer_unsoundness: allow pointer unsoundness
  void field_assignments(
    const namespacet &ns,
    goto_symex_statet &state,
    const ssa_exprt &lhs,
    const exprt &rhs,
    symex_targett &target,
    bool allow_pointer_unsoundness) const;

  /// Turn an expression \p expr into a field-sensitive SSA expression.
  /// Field-sensitive SSA expressions have individual symbols for each
  /// component. While the exact granularity is an implementation detail,
  /// possible implementations translate a struct-typed symbol into a struct of
  /// member expressions, or an array-typed symbol into an array of index
  /// expressions. Such expansions are not possible when the symbol is to be
  /// written to (i.e., \p write is true); in such a case only translations from
  /// existing member or index expressions into symbols are performed.
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param [in,out] state: symbolic execution state
  /// \param expr: an expression to be (recursively) transformed.
  /// \param write: set to true if the expression is to be used as an lvalue.
  /// \return the transformed expression
  [[nodiscard]] exprt
  apply(const namespacet &ns, goto_symex_statet &state, exprt expr, bool write)
    const;
  /// \copydoc apply(const namespacet&,goto_symex_statet&,exprt,bool) const
  [[nodiscard]] exprt apply(
    const namespacet &ns,
    goto_symex_statet &state,
    ssa_exprt expr,
    bool write) const;

  /// Compute an expression representing the individual components of a
  /// field-sensitive SSA representation of \p ssa_expr. When
  /// \p disjoined_fields_only is false, the resulting expression must be
  /// handled with care as it will have multiple operands but empty `id()`.
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param [in,out] state: symbolic execution state
  /// \param ssa_expr: the expression to evaluate
  /// \param disjoined_fields_only: whether to expand unions (`false`) or not
  ///   (`true`)
  /// \return Expanded expression; for example, for a \p ssa_expr of some struct
  ///   type, a `struct_exprt` with each component now being an SSA expression
  ///   is built.
  [[nodiscard]] exprt get_fields(
    const namespacet &ns,
    goto_symex_statet &state,
    const ssa_exprt &ssa_expr,
    bool disjoined_fields_only) const;

  /// Determine whether \p expr would translate to an atomic SSA expression
  /// (returns false) or a composite object made of several SSA expressions as
  /// components (such as a struct with each member becoming an individual SSA
  /// expression, return true in this case).
  /// \param expr: the expression to evaluate
  /// \param disjoined_fields_only: whether to expand unions (`false`) or not
  ///   (`true`)
  /// \return False, if and only if, \p expr would be a single field-sensitive
  /// SSA expression.
  [[nodiscard]] bool
  is_divisible(const ssa_exprt &expr, bool disjoined_fields_only) const;

private:
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  const std::size_t max_field_sensitivity_array_size;
#endif

  const bool should_simplify;

  void field_assignments_rec(
    const namespacet &ns,
    goto_symex_statet &state,
    const exprt &lhs_fs,
    const exprt &ssa_rhs,
    symex_targett &target,
    bool allow_pointer_unsoundness) const;

  [[nodiscard]] exprt simplify_opt(exprt e, const namespacet &ns) const;
};

#endif // CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H

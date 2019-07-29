/*******************************************************************\

Module: Field-sensitive SSA

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H
#define CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H

/// Limit the size of arrays for which field_sensitivity gets applied.
/// Necessary because large constant arrays slow-down the process.
static constexpr unsigned max_field_sensitive_array_size = 64;

class exprt;
class ssa_exprt;
class namespacet;
class goto_symex_statet;
class symex_targett;

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
/// On a high level, field sensitivity replaces member operators with atomic
/// symbols representing a field when possible. In cases where this is not
/// immediately possible, like struct assignments, some things need to be added.
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
class field_sensitivityt
{
public:
  /// Assign to the individual fields of a non-expanded symbol \p lhs. This is
  /// required whenever prior steps have updated the full object rather than
  /// individual fields, e.g., in case of assignments to an array at an unknown
  /// index.
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param state: symbolic execution state
  /// \param lhs: non-expanded symbol
  /// \param target: symbolic execution equation store
  /// \param allow_pointer_unsoundness: allow pointer unsoundness
  void field_assignments(
    const namespacet &ns,
    goto_symex_statet &state,
    const ssa_exprt &lhs,
    symex_targett &target,
    bool allow_pointer_unsoundness);

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
  exprt
  apply(const namespacet &ns, goto_symex_statet &state, exprt expr, bool write)
    const;

  /// Compute an expression representing the individual components of a
  /// field-sensitive SSA representation of \p ssa_expr.
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param [in,out] state: symbolic execution state
  /// \param ssa_expr: the expression to evaluate
  /// \return Expanded expression; for example, for a \p ssa_expr of some struct
  ///   type, a `struct_exprt` with each component now being an SSA expression
  ///   is built.
  exprt get_fields(
    const namespacet &ns,
    goto_symex_statet &state,
    const ssa_exprt &ssa_expr) const;

  /// Determine whether \p expr would translate to an atomic SSA expression
  /// (returns false) or a composite object made of several SSA expressions as
  /// components (such as a struct with each member becoming an individual SSA
  /// expression, return true in this case).
  /// \param expr: the expression to evaluate
  /// \return False, if and only if, \p expr would be a single field-sensitive
  /// SSA expression.
  static bool is_divisible(const ssa_exprt &expr);

private:
  /// whether or not to invoke \ref field_sensitivityt::apply
  bool run_apply = true;

  void field_assignments_rec(
    const namespacet &ns,
    goto_symex_statet &state,
    const exprt &lhs_fs,
    const exprt &lhs,
    symex_targett &target,
    bool allow_pointer_unsoundness);
};

#endif // CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H

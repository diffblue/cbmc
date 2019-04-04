/*******************************************************************\

Module: Field-sensitive SSA

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H
#define CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H

class exprt;
class ssa_exprt;
class namespacet;
class goto_symex_statet;
class symex_targett;

/// \brief Control granularity of object accesses
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
  void field_assignments(
    const namespacet &ns,
    goto_symex_statet &state,
    const exprt &lhs,
    symex_targett &target);

  /// Turn an expression \p expr into a field-sensitive SSA expression.
  /// Field-sensitive SSA expressions have individual symbols for each
  /// component. While the exact granularity is an implementation detail,
  /// possible implementations translate a struct-typed symbol into a struct of
  /// member expressions, or an array-typed symbol into an array of index
  /// expressions. Such expansions are not possible when the symbol is to be
  /// written to (i.e., \p write is true); in such a case only translations from
  /// existing member or index expressions into symbols are performed.
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param [in,out] expr: an expression to be (recursively) transformed - this
  ///   parameter is both input and output.
  /// \param write: set to true if the expression is to be used as an lvalue.
  void apply(const namespacet &ns, exprt &expr, bool write) const;

  /// Compute an expression representing the individual components of a
  /// field-sensitive SSA representation of \p ssa_expr.
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param ssa_expr: the expression to evaluate
  /// \return Expanded expression; for example, for a \p ssa_expr of some struct
  ///   type, a `struct_exprt` with each component now being an SSA expression
  ///   is built.
  static exprt get_fields(const namespacet &ns, const ssa_exprt &ssa_expr);

  /// Determine whether \p expr would translate to an atomic SSA expression
  /// (returns false) or a composite object made of several SSA expressions as
  /// components (such as a struct with each member becoming an individual SSA
  /// expression, return true in this case).
  /// \param ns: a namespace to resolve type symbols/tag types
  /// \param expr: the expression to evaluate
  /// \return False, if and only if, \p expr would be a single field-sensitive
  /// SSA expression.
  static bool is_divisible(const namespacet &ns, const ssa_exprt &expr);

private:
  /// whether or not to invoke \ref field_sensitivityt::apply
  bool run_apply = true;

  void field_assignments_rec(
    const namespacet &ns,
    goto_symex_statet &state,
    const exprt &lhs_fs,
    const exprt &lhs,
    symex_targett &target);
};

#endif // CPROVER_GOTO_SYMEX_FIELD_SENSITIVITY_H

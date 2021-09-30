/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

#include <vector>

#include <goto-instrument/havoc_utils.h>

#include <goto-programs/goto_model.h>

/// \brief A class that overrides the low-level havocing functions in the base
///        utility class, to havoc only when expressions point to valid memory,
///        i.e. if all dereferences within an expression are valid
class havoc_if_validt : public havoc_utilst
{
public:
  havoc_if_validt(const modifiest &mod, const namespacet &ns)
    : havoc_utilst(mod), ns(ns)
  {
  }

  void append_object_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest) const override;

  void append_scalar_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest) const override;

protected:
  const namespacet &ns;
};

/// \brief Generate a validity check over all dereferences in an expression
///
/// This function generates a formula:
///
///   good_pointer_def(pexpr_1, ns) &&
///   good_pointer_def(pexpr_2, n2) &&
///   ...
///
/// over all dereferenced pointer expressions *(pexpr_1), *(pexpr_2), ...
/// found in the AST of `expr`.
///
/// \param expr The expression that contains dereferences to be validated
/// \param ns The namespace that defines all symbols appearing in `expr`
/// \return A conjunctive expression that checks validity of all pointers
///         that are dereferenced within `expr`
exprt all_dereferences_are_valid(const exprt &expr, const namespacet &ns);

/// \brief Generate a lexicographic less-than comparison over ordered tuples
///
/// This function creates an expression representing a lexicographic less-than
/// comparison, lhs < rhs, between two ordered tuples of variables.
/// This is used in instrumentation of decreases clauses.
///
/// \param lhs A vector of variables representing the LHS of the comparison
/// \param rhs A vector of variables representing the RHS of the comparison
/// \return A lexicographic less-than comparison expression: LHS < RHS
exprt generate_lexicographic_less_than_check(
  const std::vector<symbol_exprt> &lhs,
  const std::vector<symbol_exprt> &rhs);

/// \brief Insert a goto program before a target instruction iterator
///        and advance the iterator.
///
/// This function inserts all instruction from a goto program `payload` into a
/// destination program `destination` immediately before a specified instruction
/// iterator `target`.
/// After insertion, `target` is advanced by the size of the `payload`,
/// and `payload` is destroyed.
///
/// \param destination The destination program for inserting the `payload`
/// \param target The instruction iterator at which to insert the `payload`
/// \param payload The goto program to be inserted into the `destination`
void insert_before_swap_and_advance(
  goto_programt &destination,
  goto_programt::targett &target,
  goto_programt &payload);

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

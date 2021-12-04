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

#define CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK "contracts:disable:assigns-check"

/// \brief A class that overrides the low-level havocing functions in the base
///        utility class, to havoc only when expressions point to valid memory,
///        i.e. if all dereferences within an expression are valid
class havoc_if_validt : public havoc_utilst
{
public:
  havoc_if_validt(const assignst &mod, const namespacet &ns)
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

/// \brief Adds a pragma on a GOTO instruction to disable inclusion checking.
///
/// \param instr: A mutable reference to the GOTO instruction.
/// \return The same reference after mutation (i.e., adding the pragma).
goto_programt::instructiont &
add_pragma_disable_assigns_check(goto_programt::instructiont &instr);

/// \brief Adds pragmas on all instructions in a GOTO program
///        to disable inclusion checking on them.
///
/// \param prog: A mutable reference to the GOTO program.
/// \return The same reference after mutation (i.e., adding the pragmas).
goto_programt &add_pragma_disable_assigns_check(goto_programt &prog);

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
/// \param expr: The expression that contains dereferences to be validated.
/// \param ns: The namespace that defines all symbols appearing in `expr`.
/// \return A conjunctive expression that checks validity of all pointers
///         that are dereferenced within `expr`.
exprt all_dereferences_are_valid(const exprt &expr, const namespacet &ns);

/// \brief Generate a lexicographic less-than comparison over ordered tuples
///
/// This function creates an expression representing a lexicographic less-than
/// comparison, lhs < rhs, between two ordered tuples of variables.
/// This is used in instrumentation of decreases clauses.
///
/// \param lhs: A vector of variables representing the LHS of the comparison.
/// \param rhs: A vector of variables representing the RHS of the comparison.
/// \return A lexicographic less-than comparison expression: LHS < RHS.
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
/// \param destination: The destination program for inserting the `payload`.
/// \param target: The instruction iterator at which to insert the `payload`.
/// \param payload: The goto program to be inserted into the `destination`.
void insert_before_swap_and_advance(
  goto_programt &destination,
  goto_programt::targett &target,
  goto_programt &payload);

/// \brief Adds a fresh and uniquely named symbol to the symbol table.
///
/// \param type: The type of the new symbol.
/// \param location: The source location for the new symbol.
/// \param mode: The mode for the new symbol, e.g. ID_C, ID_java.
/// \param symtab: The symbol table to which the new symbol is to be added.
/// \param suffix: Suffix to use to generate the unique name
/// \param is_auxiliary: Do not print symbol in traces if true (default = false)
/// \return The new symbolt object.
const symbolt &new_tmp_symbol(
  const typet &type,
  const source_locationt &location,
  const irep_idt &mode,
  symbol_table_baset &symtab,
  std::string suffix = "tmp_cc",
  bool is_auxiliary = false);

/// Add disable pragmas for all pointer checks on the given location
void disable_pointer_checks(source_locationt &source_location);

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

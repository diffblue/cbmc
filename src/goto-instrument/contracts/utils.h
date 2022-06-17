/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

// clang-format off
#include <vector>

#include <analyses/dirty.h>
#include <analyses/locals.h>

#include <goto-instrument/havoc_utils.h>

#include <goto-programs/goto_convert_class.h>
#include <goto-programs/goto_model.h>

#include <util/expr_cast.h>
#include <util/byte_operators.h>
#include <util/message.h>
// clang-format on

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

/// \brief A class that further overrides the "safe" havoc utilities,
///        and adds support for havocing pointer_object expressions.
class havoc_assigns_targetst : public havoc_if_validt
{
public:
  havoc_assigns_targetst(const assignst &mod, const namespacet &ns)
    : havoc_if_validt(mod, ns)
  {
  }

  void append_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest) const override;
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
/// \param is_auxiliary: Do not print symbol in traces if true (default = true)
/// \return The new symbolt object.
const symbolt &new_tmp_symbol(
  const typet &type,
  const source_locationt &location,
  const irep_idt &mode,
  symbol_table_baset &symtab,
  std::string suffix = "tmp_cc",
  bool is_auxiliary = true);

/// Turns goto instructions `IF cond GOTO label` where the condition
/// statically simplifies to `false` into SKIP instructions.
void simplify_gotos(goto_programt &goto_program, namespacet &ns);

/// Returns true iff the given program is loop-free,
/// i.e. if each SCC of its CFG contains a single element.
bool is_loop_free(
  const goto_programt &goto_program,
  namespacet &ns,
  messaget &log);

/// Allows to clean expressions of side effects.
class cleanert : public goto_convertt
{
public:
  cleanert(
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler)
    : goto_convertt(_symbol_table, _message_handler)
  {
  }

  void clean(exprt &guard, goto_programt &dest, const irep_idt &mode)
  {
    goto_convertt::clean_expr(guard, dest, mode, true);
  }

  void do_havoc_slice(
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest,
    const irep_idt &mode)
  {
    goto_convertt::do_havoc_slice(nil_exprt{}, function, arguments, dest, mode);
  }
};

/// Returns an \ref irep_idt that essentially says that
/// `target` was assigned by the contract of `function_id`.
irep_idt make_assigns_clause_replacement_tracking_comment(
  const exprt &target,
  const irep_idt &function_id,
  const namespacet &ns);

/// Returns true if the given comment matches the type of comments created by
/// \ref make_assigns_clause_replacement_tracking_comment.
bool is_assigns_clause_replacement_tracking_comment(const irep_idt &comment);

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

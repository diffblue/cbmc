/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

#include <vector>

#include <analyses/dirty.h>
#include <analyses/locals.h>

#include <goto-instrument/havoc_utils.h>

#include <goto-programs/goto_convert_class.h>
#include <goto-programs/goto_model.h>

#include <util/expr_cast.h>
#include <util/message.h>

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
/// \param is_auxiliary: Do not print symbol in traces if true (default = true)
/// \return The new symbolt object.
const symbolt &new_tmp_symbol(
  const typet &type,
  const source_locationt &location,
  const irep_idt &mode,
  symbol_table_baset &symtab,
  std::string suffix = "tmp_cc",
  bool is_auxiliary = true);

/// Add disable pragmas for all pointer checks on the given location
void disable_pointer_checks(source_locationt &source_location);

/// Turns goto instructions `IF cond GOTO label` where the condition
/// statically simplifies to `false` into SKIP instructions.
void simplify_gotos(goto_programt &goto_program, namespacet &ns);

/// Returns true iff the given program is loop-free,
/// i.e. if each SCC of its CFG contains a single element.
bool is_loop_free(
  const goto_programt &goto_program,
  namespacet &ns,
  messaget &log);

/// Stores information about a goto function computed from its CFG,
/// together with a `target` iterator into the instructions of the function.
///
/// The methods of this class provide information about identifiers at
/// the current `target` instruction to allow simplifying assigns
/// clause checking assertions.
class cfg_infot
{
public:
  cfg_infot(const namespacet &_ns, goto_functiont &_goto_function)
    : ns(_ns),
      goto_function(_goto_function),
      target(goto_function.body.instructions.begin()),
      dirty_analysis(goto_function),
      locals(goto_function)
  {
  }

  /// Steps the `target` iterator forward.
  void step()
  {
    target++;
  }

  /// Returns true iff the given `ident` is either not a `goto_function` local
  /// or is a local that is dirty.
  bool is_not_local_or_dirty_local(irep_idt ident) const
  {
    if(is_local(ident))
      return dirty_analysis.get_dirty_ids().find(ident) !=
             dirty_analysis.get_dirty_ids().end();
    else
      return true;
  }

  /// Returns true whenever the given `symbol_expr` might be alive
  /// at the current `target` instruction.
  bool is_maybe_alive(const symbol_exprt &symbol_expr)
  {
    // TODO query the static analysis when available
    return true;
  }

  /// Returns true iff `ident` is a local (or parameter) of `goto_function`.
  bool is_local(irep_idt ident) const
  {
    const auto &symbol = ns.lookup(ident);
    return locals.is_local(ident) || symbol.is_parameter;
  }

  /// returns the current target instruction
  const goto_programt::targett &get_current_target() const
  {
    return target;
  }

private:
  const namespacet &ns;
  goto_functiont &goto_function;
  goto_programt::targett target;
  const dirtyt dirty_analysis;
  const localst locals;
};

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
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

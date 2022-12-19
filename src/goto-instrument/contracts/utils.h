/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

#include <vector>

#include <goto-instrument/havoc_utils.h>

#include <goto-programs/goto_convert_class.h>

#define IN_BASE_CASE "__in_base_case"
#define ENTERED_LOOP "__entered_loop"
#define IN_LOOP_HAVOC_BLOCK "__in_loop_havoc_block"
#define INIT_INVARIANT "__init_invariant"

/// \brief A class that overrides the low-level havocing functions in the base
///        utility class, to havoc only when expressions point to valid memory,
///        i.e. if all dereferences within an expression are valid
class havoc_if_validt : public havoc_utilst
{
public:
  havoc_if_validt(const assignst &mod, const namespacet &ns)
    : havoc_utilst(mod, ns), ns(ns)
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
///   r_ok_exprt(pexpr_1, sizeof(*pexpr_1)) &&
///   r_ok_exprt(pexpr_2, sizeof(*pexpr_1)) &&
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

/// Widen expressions in \p assigns with the following strategy.
/// If an expression is an array index or object dereference expression,
/// with a non-constant offset, e.g. a[i] or *(b+i) with a non-constant `i`,
/// then replace it by the entire underlying object. Otherwise, e.g. for a[i] or
/// *(b+i) when `i` is a known constant, keep the expression in the result.
void widen_assigns(assignst &assigns, const namespacet &ns);

/// This function recursively searches \p expression to find nested or
/// non-nested quantified expressions. When a quantified expression is found,
/// a fresh quantified variable is added to the symbol table and \p expression
/// is updated to use this fresh variable.
void add_quantified_variable(
  symbol_table_baset &symbol_table,
  exprt &expression,
  const irep_idt &mode);

/// This function recursively identifies the "old" expressions within expr
/// and replaces them with correspoding history variables.
void replace_history_parameter(
  symbol_table_baset &symbol_table,
  exprt &expr,
  std::map<exprt, exprt> &parameter2history,
  source_locationt location,
  const irep_idt &mode,
  goto_programt &history,
  const irep_idt &id);

/// This function generates all the instructions required to initialize
/// history variables.
void generate_history_variables_initialization(
  symbol_table_baset &symbol_table,
  exprt &clause,
  const irep_idt &mode,
  goto_programt &program);

/// Return true if `target` is the loop end of some transformed code.
bool is_transformed_loop_end(const goto_programt::const_targett &target);

/// Return true if `target` is an assignment to an instrumented variable with
/// name `var_name`.
bool is_assignment_to_instrumented_variable(
  const goto_programt::const_targett &target,
  std::string var_name);

/// Convert the suffix digits right after `prefix` of `str` into unsigned.
unsigned get_suffix_unsigned(const std::string &str, const std::string &prefix);

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

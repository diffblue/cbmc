/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

#include <ansi-c/goto-conversion/goto_convert_class.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/loop_ids.h>

#include <analyses/local_may_alias.h>
#include <goto-instrument/havoc_utils.h>
#include <goto-instrument/loop_utils.h>

#include <vector>

#define IN_BASE_CASE "__in_base_case"
#define ENTERED_LOOP "__entered_loop"
#define IN_LOOP_HAVOC_BLOCK "__in_loop_havoc_block"
#define INIT_INVARIANT "__init_invariant"

template <class T, typename C>
class loop_templatet;
typedef std::map<loop_idt, exprt> invariant_mapt;

/// Class that allows to clean expressions of side effects and to generate
/// havoc_slice expressions.
class cleanert : public goto_convertt
{
public:
  cleanert(
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler)
    : goto_convertt(_symbol_table, _message_handler)
  {
  }

  [[nodiscard]] std::list<irep_idt>
  clean(exprt &guard, goto_programt &dest, const irep_idt &mode)
  {
    auto clean_result = goto_convertt::clean_expr(guard, mode, true);
    dest.destructive_append(clean_result.side_effects);
    return clean_result.temporaries;
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
  havoc_assigns_targetst(
    const assignst &mod,
    symbol_tablet &st,
    message_handlert &message_handler,
    const irep_idt &mode)
    : havoc_if_validt(mod, ns),
      ns(st),
      cleaner(st, message_handler),
      log(message_handler),
      mode(mode)
  {
  }

  void append_havoc_pointer_code(
    const source_locationt location,
    const exprt &ptr_to_ptr,
    goto_programt &dest);

  void append_havoc_slice_code(
    const source_locationt location,
    const exprt &ptr,
    const exprt &size,
    goto_programt &dest);

  void append_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest);

  namespacet ns;
  cleanert cleaner;
  messaget log;
  const irep_idt &mode;
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

/// \brief Insert a goto instruction before a target instruction iterator
///        and update targets of all jumps that points to the iterator to
///        jumping to the inserted instruction. This method is intended
///        to keep external instruction::targett stable, i.e. they will
///        still point to the same instruction after inserting the new one
///
/// This function inserts a instruction `i` into a destination program
/// `destination` immediately before a specified instruction iterator `target`.
/// After insertion, update all jumps that pointing to `target` to jumping to
/// `i` instead.
///
/// Different from `insert_before_swap_and_advance`, this function doesn't
/// invalidate the iterator `target` after insertion. That is, `target` and
/// all other instruction iterators same as `target` will still point to the
/// same instruction after insertion.
///
/// \param destination: The destination program for inserting the `i`.
/// \param target: The instruction iterator at which to insert the `i`.
/// \param i: The goto instruction to be inserted into the `destination`.
void insert_before_and_update_jumps(
  goto_programt &destination,
  goto_programt::targett &target,
  const goto_programt::instructiont &i);

/// Turns goto instructions `IF cond GOTO label` where the condition
/// statically simplifies to `false` into SKIP instructions.
void simplify_gotos(goto_programt &goto_program, const namespacet &ns);

/// Returns true iff the given program is loop-free,
/// i.e. if each SCC of its CFG contains a single element.
bool is_loop_free(
  const goto_programt &goto_program,
  const namespacet &ns,
  messaget &log);

/// Returns an \ref irep_idt that essentially says that
/// `target` was assigned by the contract of `function_id`.
irep_idt make_assigns_clause_replacement_tracking_comment(
  const exprt &target,
  const irep_idt &function_id,
  const namespacet &ns);

/// Returns true if the given comment matches the type of comments created by
/// \ref make_assigns_clause_replacement_tracking_comment.
bool is_assigns_clause_replacement_tracking_comment(const irep_idt &comment);

/// Infer loop assigns using alias analysis result `local_may_alias`.
void infer_loop_assigns(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  assignst &assigns);

/// Widen expressions in \p assigns with the following strategy.
/// If an expression is an array index or object dereference expression,
/// with a non-constant offset, e.g. a[i] or *(b+i) with a non-constant `i`,
/// then replace it by the entire underlying object. Otherwise, e.g. for a[i] or
/// *(b+i) when `i` is a known constant, keep the expression in the result.
void widen_assigns(assignst &assigns, const namespacet &ns);

struct replace_history_parametert
{
  exprt expression_after_replacement;
  std::unordered_map<exprt, symbol_exprt, irep_hash> parameter_to_history;
  goto_programt history_construction;
};

/// This function recursively identifies the "old" expressions within \p expr
/// and replaces them with corresponding history variables.
replace_history_parametert replace_history_old(
  symbol_table_baset &symbol_table,
  const exprt &expr,
  const source_locationt &location,
  const irep_idt &mode);

/// This function recursively identifies the "loop_entry" expressions within
/// \p expr and replaces them with corresponding history variables.
replace_history_parametert replace_history_loop_entry(
  symbol_table_baset &symbol_table,
  const exprt &expr,
  const source_locationt &location,
  const irep_idt &mode);

/// This function generates all the instructions required to initialize
/// history variables.
void generate_history_variables_initialization(
  symbol_table_baset &symbol_table,
  exprt &clause,
  const irep_idt &mode,
  goto_programt &program);

/// Return true if `target` is the head of some transformed loop.
bool is_transformed_loop_head(const goto_programt::const_targett &target);

/// Return true if `target` is the end of some transformed loop.
bool is_transformed_loop_end(const goto_programt::const_targett &target);

/// Return true if `target` is an assignment to an instrumented variable with
/// name `var_name`.
bool is_assignment_to_instrumented_variable(
  const goto_programt::const_targett &target,
  std::string var_name);

/// Convert the suffix digits right after `prefix` of `str` into unsigned.
unsigned get_suffix_unsigned(const std::string &str, const std::string &prefix);

/// Find the goto instruction of `loop` that jumps to `loop_head`
goto_programt::targett get_loop_end_from_loop_head_and_content_mutable(
  const goto_programt::targett &loop_head,
  const loop_templatet<goto_programt::targett, goto_programt::target_less_than>
    &loop);

goto_programt::const_targett get_loop_end_from_loop_head_and_content(
  const goto_programt::const_targett &loop_head,
  const loop_templatet<
    goto_programt::const_targett,
    goto_programt::target_less_than> &loop);

/// Return loop head if `finding_head` is true,
/// Otherwise return loop end.
goto_programt::targett get_loop_head_or_end(
  const unsigned int loop_number,
  goto_functiont &function,
  bool finding_head);

/// Find and return the last instruction of the natural loop with
/// `loop_number` in `function`. loop_end -> loop_head
goto_programt::targett
get_loop_end(const unsigned int loop_number, goto_functiont &function);

/// Find and return the first instruction of the natural loop with
/// `loop_number` in `function`. loop_end -> loop_head
goto_programt::targett
get_loop_head(const unsigned int loop_number, goto_functiont &function);

/// Extract loop invariants from annotated loop end.
/// Will check if the loop invariant is side-effect free if
/// \p check_side_effect` is set.
exprt get_loop_invariants(
  const goto_programt::const_targett &loop_end,
  const bool check_side_effect = true);

/// Extract loop assigns from annotated loop end.
exprt get_loop_assigns(const goto_programt::const_targett &loop_end);

/// Extract loop decreases from annotated loop end.
/// Will check if the loop decreases is side-effect free if
/// \p check_side_effect` is set.
exprt get_loop_decreases(
  const goto_programt::const_targett &loop_end,
  const bool check_side_effect = true);

/// Annotate the invariants in `invariant_map` to their corresponding
/// loops. Corresponding loops are specified by keys of `invariant_map`
void annotate_invariants(
  const invariant_mapt &invariant_map,
  goto_modelt &goto_model);

/// Annotate the assigns in `assigns_map` to their corresponding
/// loops. Corresponding loops are specified by keys of `assigns_map`
void annotate_assigns(
  const std::map<loop_idt, std::set<exprt>> &assigns_map,
  goto_modelt &goto_model);

void annotate_assigns(
  const std::map<loop_idt, exprt> &assigns_map,
  goto_modelt &goto_model);

/// Annotate the decreases in `decreases_map` to their corresponding
/// loops. Corresponding loops are specified by keys of `decreases_map`
void annotate_decreases(
  const std::map<loop_idt, std::vector<exprt>> &decreases_map,
  goto_modelt &goto_model);

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_H

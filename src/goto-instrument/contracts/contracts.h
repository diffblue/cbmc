/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_H

#include <map>
#include <set>
#include <string>
#include <unordered_set>

#include <goto-instrument/loop_utils.h>

#include <goto-programs/goto_convert_class.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <langapi/language_util.h>

#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>

#define FLAG_LOOP_CONTRACTS "apply-loop-contracts"
#define HELP_LOOP_CONTRACTS                                                    \
  " --apply-loop-contracts\n"                                                  \
  "                              check and use loop contracts when provided\n"

#define FLAG_REPLACE_CALL "replace-call-with-contract"
#define HELP_REPLACE_CALL                                                      \
  " --replace-call-with-contract <fun>\n"                                      \
  "                              replace calls to fun with fun's contract\n"

#define FLAG_REPLACE_ALL_CALLS "replace-all-calls-with-contracts"
#define HELP_REPLACE_ALL_CALLS                                                 \
  " --replace-all-calls-with-contracts\n"                                      \
  "                              as above for all functions with a contract\n"

#define FLAG_ENFORCE_CONTRACT "enforce-contract"
#define HELP_ENFORCE_CONTRACT                                                  \
  " --enforce-contract <fun>     wrap fun with an assertion of its contract\n"

#define FLAG_ENFORCE_ALL_CONTRACTS "enforce-all-contracts"
#define HELP_ENFORCE_ALL_CONTRACTS                                             \
  " --enforce-all-contracts      as above for all functions with a contract\n"

class assigns_clauset;
class local_may_aliast;
class replace_symbolt;

class code_contractst
{
public:
  code_contractst(goto_modelt &goto_model, messaget &log)
    : ns(goto_model.symbol_table),
      symbol_table(goto_model.symbol_table),
      goto_functions(goto_model.goto_functions),
      log(log),
      converter(symbol_table, log.get_message_handler())

  {
  }

  /// \brief Replace all calls to each function in the list with that function's
  ///        contract
  ///
  /// Use this function when proving code that calls into an expensive function,
  /// `F`. You can write a contract for F using __CPROVER_requires and
  /// __CPROVER_ensures, and then use this function to replace all calls to `F`
  /// with an assertion that the `requires` clause holds followed by an
  /// assumption that the `ensures` clause holds. In order to ensure that `F`
  /// actually abides by its `ensures` and `requires` clauses, you should
  /// separately call `code_constractst::enforce_contracts()` on `F` and verify
  /// it using `cbmc --function F`.
  ///
  /// \return `true` on failure, `false` otherwise
  bool replace_calls(const std::set<std::string> &functions);

  /// \brief Turn requires & ensures into assumptions and assertions for each of
  ///        the named functions
  ///
  /// Use this function to prove the correctness of a function F independently
  /// of its calling context. If you have proved that F is correct, then you can
  /// soundly replace all calls to F with F's contract using the
  /// code_contractst::replace_calls() function; this means that symbolic
  /// execution does not need to explore F every time it is called, increasing
  /// scalability.
  ///
  /// Implementation: mangle the name of each function F into a new name,
  /// `__CPROVER_contracts_original_F` (`CF` for short). Then mint a new
  /// function called `F` that assumes `CF`'s `requires` clause, calls `CF`, and
  /// then asserts `CF`'s `ensures` clause.
  ///
  /// \return `true` on failure, `false` otherwise
  bool enforce_contracts(const std::set<std::string> &functions);

  /// \brief Call enforce_contracts() on all functions that have a contract
  /// \return `true` on failure, `false` otherwise
  bool enforce_contracts();

  /// \brief Call replace_calls() on all calls to any function that has a
  ///        contract
  /// \return `true` on failure, `false` otherwise
  bool replace_calls();

  void apply_loop_contracts();

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location,
    const irep_idt &mode);

  void check_apply_loop_contracts(
    goto_functionst::goto_functiont &goto_function,
    const local_may_aliast &local_may_alias,
    goto_programt::targett loop_head,
    const loopt &loop,
    const irep_idt &mode);

  // for "helper" classes to update symbol table.
  symbol_tablet &get_symbol_table();
  goto_functionst &get_goto_functions();

  namespacet ns;

protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  messaget &log;
  goto_convertt converter;

  std::unordered_set<irep_idt> summarized;

  /// \brief Enforce contract of a single function
  bool enforce_contract(const irep_idt &function);

  /// Instrument functions to check frame conditions.
  bool check_frame_conditions_function(const irep_idt &function);

  /// Insert assertion statements into the goto program to ensure that
  /// assigned memory is within the assignable memory frame.
  void check_frame_conditions(goto_programt &program, const symbolt &target);

  /// Check if there are any malloc statements which may be repeated because of
  /// a goto statement that jumps back.
  bool check_for_looped_mallocs(const goto_programt &program);

  /// Inserts an assertion statement into program before the assignment
  /// instruction_it, to ensure that the left-hand-side of the assignment
  /// aliases some expression in original_references, unless it is contained
  /// in freely_assignable_exprs.
  void instrument_assign_statement(
    goto_programt::instructionst::iterator &instruction_it,
    goto_programt &program,
    exprt &assigns,
    std::set<irep_idt> &freely_assignable_symbols,
    assigns_clauset &assigns_clause);

  /// Inserts an assertion statement into program before the function call at
  /// ins_it, to ensure that any memory which may be written by the call is
  /// aliased by some expression in assigns_references,unless it is contained
  /// in freely_assignable_exprs.
  void instrument_call_statement(
    goto_programt::instructionst::iterator &ins_it,
    goto_programt &program,
    exprt &assigns,
    std::set<irep_idt> &freely_assignable_symbols,
    assigns_clauset &assigns_clause);

  /// Creates a boolean expression which is true when there exists an expression
  /// in aliasable_references with the same pointer object and pointer offset as
  /// the address of lhs.
  exprt create_alias_expression(
    const exprt &lhs,
    std::vector<exprt> &aliasable_references);

  /// Apply loop contracts, whenever available, to all loops in `function`.
  /// Loop invariants, loop variants, and loop assigns clauses.
  void apply_loop_contract(
    const irep_idt &function,
    goto_functionst::goto_functiont &goto_function);

  /// \brief Does the named function have a contract?
  bool has_contract(const irep_idt);

  /// Replaces function calls with assertions based on requires clauses,
  /// non-deterministic assignments for the write set, and assumptions
  /// based on ensures clauses.
  bool apply_function_contract(
    goto_programt &goto_program,
    goto_programt::targett target);

  /// Instruments `wrapper_function` adding assumptions based on requires
  /// clauses and assertions based on ensures clauses.
  void add_contract_check(
    const irep_idt &wrapper_function,
    const irep_idt &mangled_function,
    goto_programt &dest);

  /// This function recursively searches the expression to find nested or
  /// non-nested quantified expressions. When a quantified expression is found,
  /// the quantified variable is added to the symbol table
  /// and to the expression map.
  void add_quantified_variable(
    const exprt &expression,
    replace_symbolt &replace,
    const irep_idt &mode);

  /// This function recursively identifies the "old" expressions within expr
  /// and replaces them with correspoding history variables.
  void replace_old_parameter(
    exprt &expr,
    std::map<exprt, exprt> &parameter2history,
    source_locationt location,
    const irep_idt &mode,
    goto_programt &history);

  /// This function creates and returns an instruction that corresponds to the
  /// ensures clause. It also returns a list of instructions related to
  /// initializing history variables, if required.
  std::pair<goto_programt, goto_programt> create_ensures_instruction(
    codet &expression,
    source_locationt location,
    const irep_idt &mode);
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_H

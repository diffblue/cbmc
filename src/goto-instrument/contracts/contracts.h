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
#include <goto-programs/instrument_preconditions.h>

#include <util/message.h>
#include <util/namespace.h>
#include <util/optional.h>
#include <util/pointer_expr.h>

#define FLAG_LOOP_CONTRACTS "apply-loop-contracts"
#define HELP_LOOP_CONTRACTS                                                    \
  " --apply-loop-contracts\n"                                                  \
  "                              check and use loop contracts when provided\n"

#define FLAG_REPLACE_CALL "replace-call-with-contract"
#define HELP_REPLACE_CALL                                                      \
  " --replace-call-with-contract <fun>\n"                                      \
  "                              replace calls to fun with fun's contract\n"

#define FLAG_ENFORCE_CONTRACT "enforce-contract"
#define HELP_ENFORCE_CONTRACT                                                  \
  " --enforce-contract <fun>     wrap fun with an assertion of its contract\n"

class local_may_aliast;
class replace_symbolt;
class instrument_spec_assignst;
class cfg_infot;

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

  /// Throws an exception if some function `functions` is found in the program.
  void check_all_functions_found(const std::set<std::string> &functions) const;

  /// \brief Replace all calls to each function in the `to_replace` set
  /// with that function's contract
  ///
  /// Throws an exception if some `to_replace` functions are not found.
  ///
  /// Use this function when proving code that calls into an expensive function,
  /// `F`. You can write a contract for F using __CPROVER_requires and
  /// __CPROVER_ensures, and then use this function to replace all calls to `F`
  /// with an assertion that the `requires` clause holds followed by an
  /// assumption that the `ensures` clause holds. In order to ensure that `F`
  /// actually abides by its `ensures` and `requires` clauses, you should
  /// separately call `code_constractst::enforce_contracts()` on `F` and verify
  /// it using `cbmc --function F`.
  void replace_calls(const std::set<std::string> &to_replace);

  /// \brief Turn requires & ensures into assumptions and assertions for each of
  ///        the named functions
  ///
  /// Throws an exception if some `to_enforce` functions are not found.
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
  void enforce_contracts(const std::set<std::string> &to_enforce);

  void apply_loop_contracts();

  void check_apply_loop_contracts(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &goto_function,
    const local_may_aliast &local_may_alias,
    goto_programt::targett loop_head,
    goto_programt::targett loop_end,
    const loopt &loop,
    exprt assigns_clause,
    exprt invariant,
    exprt decreases_clause,
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
  void enforce_contract(const irep_idt &function);

  /// Instrument functions to check frame conditions.
  void check_frame_conditions_function(const irep_idt &function);

  /// Apply loop contracts, whenever available, to all loops in `function`.
  /// Loop invariants, loop variants, and loop assigns clauses.
  void apply_loop_contract(
    const irep_idt &function,
    goto_functionst::goto_functiont &goto_function);

  /// Replaces function calls with assertions based on requires clauses,
  /// non-deterministic assignments for the write set, and assumptions
  /// based on ensures clauses.
  void apply_function_contract(
    const irep_idt &function,
    const source_locationt &location,
    goto_programt &function_body,
    goto_programt::targett &target);

  /// Instruments `wrapper_function` adding assumptions based on requires
  /// clauses and assertions based on ensures clauses.
  void add_contract_check(
    const irep_idt &wrapper_function,
    const irep_idt &mangled_function,
    goto_programt &dest);

  /// This function recursively searches \p expression to find nested or
  /// non-nested quantified expressions. When a quantified expression is found,
  /// a fresh quantified variable is added to the symbol table and \p expression
  /// is updated to use this fresh variable.
  void add_quantified_variable(exprt &expression, const irep_idt &mode);

  /// This function recursively identifies the "old" expressions within expr
  /// and replaces them with correspoding history variables.
  void replace_history_parameter(
    exprt &expr,
    std::map<exprt, exprt> &parameter2history,
    source_locationt location,
    const irep_idt &mode,
    goto_programt &history,
    const irep_idt &id);

  /// This function creates and returns an instruction that corresponds to the
  /// ensures clause. It also returns a list of instructions related to
  /// initializing history variables, if required.
  std::pair<goto_programt, goto_programt> create_ensures_instruction(
    codet &expression,
    source_locationt location,
    const irep_idt &mode);
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_H

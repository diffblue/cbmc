/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_H

#include <util/message.h>
#include <util/namespace.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <goto-instrument/loop_utils.h>

#include "loop_contract_config.h"

#include <map>
#include <set>
#include <string>
#include <unordered_set>

#define FLAG_LOOP_CONTRACTS "apply-loop-contracts"
#define HELP_LOOP_CONTRACTS                                                    \
  " {y--apply-loop-contracts} \t check and use loop contracts when provided\n"

#define FLAG_DISABLE_SIDE_EFFECT_CHECK                                         \
  "disable-loop-contracts-side-effect-check"
#define HELP_DISABLE_SIDE_EFFECT_CHECK                                         \
  " {y--disable-loop-contracts-side-effect-check} \t UNSOUND OPTION.\t "       \
  " disable the check of side-effect of loop contracts\n"
#define FLAG_LOOP_CONTRACTS_NO_UNWIND "loop-contracts-no-unwind"
#define HELP_LOOP_CONTRACTS_NO_UNWIND                                          \
  " {y--loop-contracts-no-unwind} \t do not unwind transformed loops\n"

#define FLAG_LOOP_CONTRACTS_FILE "loop-contracts-file"
#define HELP_LOOP_CONTRACTS_FILE                                               \
  " {y--loop-contracts-file} {ufile} \t "                                      \
  "parse and annotate loop contracts from files\n"

#define FLAG_REPLACE_CALL "replace-call-with-contract"
#define HELP_REPLACE_CALL                                                      \
  " {y--replace-call-with-contract} {ufunction}[/{ucontract}] \t "             \
  "replace calls to {ufunction} with {ucontract}\n"

#define FLAG_ENFORCE_CONTRACT "enforce-contract"
#define HELP_ENFORCE_CONTRACT                                                  \
  " {y--enforce-contract} {ufunction}[/{ucontract}] \t "                       \
  "wrap function with an assertion of contract\n"

class local_may_aliast;

class code_contractst
{
public:
  code_contractst(
    goto_modelt &goto_model,
    messaget &log,
    const loop_contract_configt &loop_contract_config)
    : ns(goto_model.symbol_table),
      goto_model(goto_model),
      symbol_table(goto_model.symbol_table),
      goto_functions(goto_model.goto_functions),
      log(log),
      loop_contract_config(loop_contract_config)
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
  /// separately call `code_contractst::enforce_contracts()` on `F` and verify
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
  /// Static variables of the model are nondet-initialized, except for the ones
  /// specified in to_exclude_from_nondet_init.
  ///
  /// Implementation: mangle the name of each function F into a new name,
  /// `__CPROVER_contracts_original_F` (`CF` for short). Then mint a new
  /// function called `F` that assumes `CF`'s `requires` clause, calls `CF`, and
  /// then asserts `CF`'s `ensures` clause.
  ///
  void enforce_contracts(
    const std::set<std::string> &to_enforce,
    const std::set<std::string> &to_exclude_from_nondet_init = {});

  /// Applies loop contract transformations.
  /// Static variables of the model are nondet-initialized, except for the ones
  /// specified in to_exclude_from_nondet_init.
  void apply_loop_contracts(
    const std::set<std::string> &to_exclude_from_nondet_init = {});

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

  std::unordered_map<goto_programt::const_targett, unsigned, const_target_hash>
  get_original_loop_number_map() const
  {
    return original_loop_number_map;
  }

  std::unordered_set<goto_programt::const_targett, const_target_hash>
  get_loop_havoc_set() const
  {
    return loop_havoc_set;
  }

  const namespacet ns;

protected:
  goto_modelt &goto_model;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  messaget &log;

  std::unordered_set<irep_idt> summarized;

  /// Name of loops we are going to unwind.
  std::list<std::string> loop_names;

  /// Store the map from instrumented instructions for loop contracts to their
  /// original loop numbers. Following instrumented instructions are stored.
  /// 1. loop-havoc   ---   begin of transformed loops
  /// 2. ASSIGN ENTERED_LOOP = TRUE   ---   end of transformed loops
  std::unordered_map<goto_programt::const_targett, unsigned, const_target_hash>
    original_loop_number_map;

  /// Loop havoc instructions instrumented during applying loop contracts.
  std::unordered_set<goto_programt::const_targett, const_target_hash>
    loop_havoc_set;

  // Loop contract configuration
  loop_contract_configt loop_contract_config;

public:
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
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_H

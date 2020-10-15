/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

#include <set>
#include <string>
#include <unordered_set>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <util/namespace.h>

class messaget;

class code_contractst
{
public:
  code_contractst(goto_modelt &goto_model, messaget &log)
    : ns(goto_model.symbol_table),
      symbol_table(goto_model.symbol_table),
      goto_functions(goto_model.goto_functions),
      temporary_counter(0),
      log(log)
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
  bool replace_calls(const std::set<std::string> &);

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
  bool enforce_contracts(const std::set<std::string> &);

  /// \brief Call enforce_contracts() on all functions that have a contract
  /// \return `true` on failure, `false` otherwise
  bool enforce_contracts();

  /// \brief Call replace_calls() on all calls to any function that has a
  ///        contract
  /// \return `true` on failure, `false` otherwise
  bool replace_calls();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  unsigned temporary_counter;
  messaget &log;

  std::unordered_set<irep_idt> summarized;

  /// \brief Enforce contract of a single function
  bool enforce_contract(const std::string &);

  /// Insert assertion statements into the goto program to ensure that
  /// assigned memory is within the assignable memory frame.
  bool add_pointer_checks(const std::string &);

  /// Check if there are any malloc statements which may be repeated because of
  /// a goto statement that jumps back.
  bool check_for_looped_mallocs(const goto_programt &);

  /// Inserts an assertion statement into program before the assignment ins_it,
  /// to ensure that the left-hand-side of the assignment aliases some
  /// expression in original_references, unless it is contained in
  /// freely_assignable_exprs.
  void instrument_assigns_statement(
    goto_programt::instructionst::iterator &ins_it,
    goto_programt &program,
    exprt &assigns,
    std::vector<exprt> &original_references,
    std::set<exprt> &freely_assignable_exprs);

  /// Inserts an assertion statement into program before the function call at
  /// ins_it, to ensure that any memory which may be written by the call is
  /// aliased by some expression in assigns_references,unless it is contained
  /// in freely_assignable_exprs.
  void instrument_call_statement(
    goto_programt::instructionst::iterator &ins_it,
    goto_programt &program,
    exprt &assigns,
    std::vector<exprt> &assigns_references,
    std::set<exprt> &freely_assignable_exprs);

  /// Creates a local variable declaration for each expression in the assigns
  /// clause (of the function given by f_sym), and stores them in created_decls.
  /// Then creates assignment statements to capture the memory addresses of each
  /// expression in the assigns clause within the associated local variable,
  /// populating a vector created_references of these local variables.
  void populate_assigns_references(
    const symbolt &f_sym,
    const irep_idt &func_id,
    goto_programt &created_decls,
    std::vector<exprt> &created_references);

  void code_contracts(goto_functionst::goto_functiont &goto_function);

  /// \brief Does the named function have a contract?
  bool has_contract(const irep_idt);

  bool
  apply_contract(goto_programt &goto_program, goto_programt::targett target);

  void
  add_contract_check(const irep_idt &, const irep_idt &, goto_programt &dest);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location,
    const irep_idt &function_id,
    const irep_idt &mode);
};

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

#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

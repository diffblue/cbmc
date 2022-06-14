/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for ANSI-C

#ifndef CPROVER_GOTO_CHECKER_SYMEX_BMC_H
#define CPROVER_GOTO_CHECKER_SYMEX_BMC_H

#include <util/threeval.h>

#include <goto-symex/goto_symex.h>

#include "symex_coverage.h"

class unwindsett;

class symex_bmct : public goto_symext
{
public:
  symex_bmct(
    message_handlert &mh,
    const symbol_tablet &outer_symbol_table,
    symex_target_equationt &_target,
    const optionst &options,
    path_storaget &path_storage,
    guard_managert &guard_manager,
    unwindsett &unwindset);

  // To show progress
  source_locationt last_source_location;

  /// Loop unwind handlers take the call stack, loop number, the unwind count so
  /// far, and an out-parameter specifying an advisory maximum, which they may
  /// set. If set the advisory maximum is set it is *only* used to print useful
  /// information for the user (e.g. "unwinding iteration N, max M"), and is not
  /// enforced. They return true to halt unwinding, false to authorise
  /// unwinding, or Unknown to indicate they have no opinion.
  typedef std::function<
    tvt(const call_stackt &, unsigned, unsigned, unsigned &)>
    loop_unwind_handlert;

  /// Recursion unwind handlers take the function ID, the unwind count so far,
  /// and an out-parameter specifying an advisory maximum, which they may set.
  /// If set the advisory maximum is set it is *only* used to print useful
  /// information for the user (e.g. "unwinding iteration N, max M"),
  /// and is not enforced. They return true to halt unwinding, false to
  /// authorise unwinding, or Unknown to indicate they have no opinion.
  typedef std::function<tvt(const irep_idt &, unsigned, unsigned &)>
    recursion_unwind_handlert;

  /// Add a callback function that will be called to determine whether to unwind
  /// loops. The first function added will get the first chance to answer, and
  /// the first authoratitive (true or false) answer is final.
  /// \param handler: new callback
  void add_loop_unwind_handler(loop_unwind_handlert handler)
  {
    loop_unwind_handlers.push_back(handler);
  }

  /// Add a callback function that will be called to determine whether to unwind
  /// recursion. The first function added will get the first chance to answer,
  /// and the first authoratitive (true or false) answer is final.
  /// \param handler: new callback
  void add_recursion_unwind_handler(recursion_unwind_handlert handler)
  {
    recursion_unwind_handlers.push_back(handler);
  }

  bool output_coverage_report(
    const goto_functionst &goto_functions,
    const std::string &path) const
  {
    return symex_coverage.generate_report(goto_functions, path);
  }

  const bool record_coverage;
  const bool havoc_bodyless_functions;

  unwindsett &unwindset;

  const symex_coveraget get_coverage () const;

protected:
  /// Callbacks that may provide an unwind/do-not-unwind decision for a loop
  std::vector<loop_unwind_handlert> loop_unwind_handlers;

  /// Callbacks that may provide an unwind/do-not-unwind decision for a
  /// recursive call
  std::vector<recursion_unwind_handlert> recursion_unwind_handlers;

  void symex_step(const get_goto_functiont &get_goto_function, statet &state)
    override;

  void merge_goto(
    const symex_targett::sourcet &source,
    goto_statet &&goto_state,
    statet &state) override;

  bool should_stop_unwind(
    const symex_targett::sourcet &source,
    const call_stackt &context,
    unsigned unwind) override;

  bool get_unwind_recursion(
    const irep_idt &identifier,
    unsigned thread_nr,
    unsigned unwind) override;

  void no_body(const irep_idt &identifier) override;

  std::unordered_set<irep_idt> body_warnings;

  symex_coveraget symex_coverage;
};

#endif // CPROVER_GOTO_CHECKER_SYMEX_BMC_H

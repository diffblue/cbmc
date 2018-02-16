/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for ANSI-C

#ifndef CPROVER_CBMC_SYMEX_BMC_H
#define CPROVER_CBMC_SYMEX_BMC_H

#include <util/message.h>
#include <util/threeval.h>

#include <goto-symex/goto_symex.h>

#include "symex_coverage.h"

class symex_bmct: public goto_symext
{
public:
  symex_bmct(
    message_handlert &mh,
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    symex_targett &_target);

  // To show progress
  source_locationt last_source_location;

  // Control unwinding.

  void set_unwind_limit(unsigned limit)
  {
    max_unwind=limit;
    max_unwind_is_set=true;
  }

  void set_unwind_thread_loop_limit(
    unsigned thread_nr,
    const irep_idt &id,
    unsigned limit)
  {
    thread_loop_limits[thread_nr][id]=limit;
  }

  void set_unwind_loop_limit(
    const irep_idt &id,
    unsigned limit)
  {
    loop_limits[id]=limit;
  }

  /// Loop unwind handlers take the function ID and loop number, the unwind
  /// count so far, and an out-parameter specifying an advisory maximum, which
  /// they may set. If set the advisory maximum is set it is *only* used to
  /// print useful information for the user (e.g. "unwinding iteration N, max
  /// M"), and is not enforced. They return true to halt unwinding, false to
  /// authorise unwinding, or Unknown to indicate they have no opinion.
  typedef
    std::function<tvt(const irep_idt &, unsigned, unsigned, unsigned &)>
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

  bool record_coverage;

protected:
  // We have
  // 1) a global limit (max_unwind)
  // 2) a limit per loop, all threads
  // 3) a limit for a particular thread.
  // 4) zero or more handler functions that can special-case particular
  //    functions or loops
  // We use the most specific of the above.

  unsigned max_unwind;
  bool max_unwind_is_set;

  typedef std::unordered_map<irep_idt, unsigned, irep_id_hash> loop_limitst;
  loop_limitst loop_limits;

  typedef std::map<unsigned, loop_limitst> thread_loop_limitst;
  thread_loop_limitst thread_loop_limits;

  /// Callbacks that may provide an unwind/do-not-unwind decision for a loop
  std::vector<loop_unwind_handlert> loop_unwind_handlers;
  /// Callbacks that may provide an unwind/do-not-unwind decision for a
  /// recursive call
  std::vector<recursion_unwind_handlert> recursion_unwind_handlers;

  //
  // overloaded from goto_symext
  //
  virtual void symex_step(
    const get_goto_functiont &get_goto_function,
    statet &state);

  virtual void merge_goto(
    const statet::goto_statet &goto_state,
    statet &state);

  // for loop unwinding
  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    unsigned unwind);

  virtual bool get_unwind_recursion(
    const irep_idt &identifier,
    const unsigned thread_nr,
    unsigned unwind);

  virtual void no_body(const irep_idt &identifier);

  std::unordered_set<irep_idt, irep_id_hash> body_warnings;

  symex_coveraget symex_coverage;
};

#endif // CPROVER_CBMC_SYMEX_BMC_H

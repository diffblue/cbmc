/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for ANSI-C

#ifndef CPROVER_CBMC_SYMEX_BMC_H
#define CPROVER_CBMC_SYMEX_BMC_H

#include <util/message.h>

#include <langapi/language_ui.h>

#include <goto-symex/goto_symex.h>

#include "symex_coverage.h"

class symex_bmct:
  public goto_symext,
  public messaget
{
public:
  symex_bmct(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    symex_targett &_target);

  void set_ui(language_uit::uit _ui) { ui=_ui; }

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

  bool output_coverage_report(
    const goto_functionst &goto_functions,
    const std::string &path) const
  {
    return symex_coverage.generate_report(goto_functions, path);
  }

  bool record_coverage;

protected:
  // use gui format
  language_uit::uit ui;

  // We have
  // 1) a global limit (max_unwind)
  // 2) a limit per loop, all threads
  // 3) a limit for a particular thread.
  // We use the most specific of the above.

  unsigned max_unwind;
  bool max_unwind_is_set;

  typedef std::unordered_map<irep_idt, unsigned, irep_id_hash> loop_limitst;
  loop_limitst loop_limits;

  typedef std::map<unsigned, loop_limitst> thread_loop_limitst;
  thread_loop_limitst thread_loop_limits;

  //
  // overloaded from goto_symext
  //
  virtual bool symex_step(
    const goto_functionst &goto_functions,
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

/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_PARSEOPTIONS_H
#define CPROVER_GOTO_INSTRUMENT_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>
#include <goto-programs/goto_functions.h>

#define GOTO_INSTRUMENT_OPTIONS \
  "(all)" \
  "(document-claims-latex)(document-claims-html)" \
  "(document-properties-latex)(document-properties-html)" \
  "(dump-c)(dump-cpp)(use-system-headers)(dot)(xml)" \
  "(bounds-check)(no-bounds-check)" \
  "(pointer-check)(memory-leak-check)(no-pointer-check)" \
  "(static-pointer-check)" \
  "(which-threads)" \
  "(remove-pointers)" \
  "(no-simplify)" \
  "(assert-to-assume)" \
  "(div-by-zero-check)(no-div-by-zero-check)" \
  "(undefined-shift-check)" \
  "(no-assertions)(no-assumptions)(uninitialized-check)" \
  "(nan-check)(no-nan-check)" \
  "(race-check)(scc)(one-event-per-cycle)" \
  "(minimum-interference)" \
  "(mm):(my-events)(unwind):" \
  "(max-var):(max-po-trans):(ignore-arrays)" \
  "(cfg-kill)(no-dependencies)(force-loop-duplication)" \
  "(call-graph)" \
  "(no-po-rendering)(render-cluster-file)(render-cluster-function)" \
  "(nondet-volatile)(isr):" \
  "(stack-depth):(nondet-static)" \
  "(function-enter):(function-exit):(branch):" \
  "(signed-overflow-check)(unsigned-overflow-check)(float-overflow-check)" \
  "(show-goto-functions)(show-value-sets)(show-local-may-alias)" \
  "(show-sharing)(show-lock-sets)(show-deadlocks)" \
  "(create-thread-function):(create-thread-arg-no):(create-thread-arg-no-of-arg):(join-thread-function):" \
  "(lock-function):(unlock-function):" \
  "(escape-analysis)(show-escape-analysis)" \
  "(custom-bitvector-analysis)(show-custom-bitvector-analysis)" \
  "(show-struct-alignment)(interval-analysis)(show-intervals)" \
  "(show-uninitialized)(show-locations)" \
  "(full-slice)(reachability-slice)" \
  "(inline)" \
  "(show-claims)(show-properties)" \
  "(show-symbol-table)(show-points-to)(show-rw-set)" \
  "(cav11)" \
  "(show-natural-loops)(accelerate)(havoc-loops)" \
  "(error-label):(string-abstraction)" \
  "(verbosity):(version)(xml-ui)(show-loops)" \
  "(accelerate)(constant-propagator)" \
  "(k-induction):(step-case)(base-case)" \
  "(show-call-sequences)(check-call-sequence)" \
  "(interpreter)(show-reaching-definitions)(count-eloc)" \
  "(list-symbols)(list-undefined-functions)" \
  "(z3)(add-library)(show-dependence-graph)" \
  "(horn)(skip-loops):" \
  "(show-dominators):(show-post-dominators):(dominator-start):" \
  "(non-concurrent)(is-lock-protected)(is-non-concurrent)" \
  "(stack1):(stack2):(loc1):(loc2):" \
  "(print-reachable)" \
  "(check-reachable)(stack):(loc):" \
  "(check-stack):" \
  "(has-path):(on-all-paths):" \
  "(in-loop):" \
  "(show-may-lock-sets)(show-must-lock-sets)" \
  "(print-locks)" \
  "(print-option):" \
  "(remove-function-pointers)" \
  "(check-instructions)" \
  "(show-lock-dependencies-simple)" \
  "(show-lock-dependencies-global)" \
  "(show-branch-dependencies-global)" \
  "(remove-returns)" \
  "(print-code):" \
  "(show-value-sets-fi)" \
  "(flow-insensitive-value-set-analysis)" \
  "(simple-dependency-analysis-ii)" \
  "(simple-dependency-analysis-is)" \
  "(show-non-concurrency-stats)" \
  "(show-framework-stats)" \
  "(use-trie-numbering)" \
  "(show-simple-dependency-analysis-stats)"

class goto_instrument_parse_optionst:
  public parse_options_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  goto_instrument_parse_optionst(int argc, const char **argv):
    parse_options_baset(GOTO_INSTRUMENT_OPTIONS, argc, argv),
    language_uit("goto-instrument", cmdline),
    function_pointer_removal_done(false),
    partial_inlining_done(false),
    remove_returns_done(false)
  {
  }
  
protected:
  virtual void register_languages();

  void get_goto_program();
  void instrument_goto_program();
    
  void eval_verbosity();
  
  void do_function_pointer_removal();
  void do_partial_inlining();
  void do_remove_returns();
  
  // workaround for wrong function tags in locations
  void sanitize_location_tags();

  bool function_pointer_removal_done;
  bool partial_inlining_done;
  bool remove_returns_done;
  
  goto_functionst goto_functions;
};

#endif

/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for ANSI-C + HDL

#ifndef CPROVER_CBMC_BMC_H
#define CPROVER_CBMC_BMC_H

#include <list>
#include <map>

#include <util/invariant.h>
#include <util/options.h>
#include <util/ui_message.h>

#include <java_bytecode/java_enum_static_init_unwind_handler.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <solvers/smt2/smt2_dec.h>

#include <goto-programs/goto_trace.h>

#include <goto-symex/symex_target_equation.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/safety_checker.h>
#include <goto-symex/memory_model.h>

#include "symex_bmc.h"

class cbmc_solverst;

/// \brief Bounded model checking or path exploration for goto-programs
///
/// Higher-level architectural information on symbolic execution is
/// documented in the \ref symex-overview
/// "Symbolic execution module page".
class bmct:public safety_checkert
{
public:
  /// \brief Constructor for path exploration with freshly-initialized state
  ///
  /// This constructor should be used for symbolically executing a program
  /// from the entry point with fresh state. There are two main behaviours
  /// that can happen when constructing an instance of this class:
  ///
  /// - If the `--paths` flag in the `options` argument to this
  ///   constructor is `false` (unset), an instance of this class will
  ///   symbolically execute the entire program, performing path merging
  ///   to build a formula corresponding to all executions of the program
  ///   up to the unwinding limit. In this case, the `branch_worklist`
  ///   member shall not be touched; this is enforced by the assertion in
  ///   this class' implementation of bmct::perform_symbolic_execution().
  ///
  /// - If the `--paths` flag is `true`, this `bmct` object will explore a
  ///   single path through the codebase without doing any path merging.
  ///   If some paths were not taken, the state at those branch points
  ///   will be appended to `branch_worklist`. After the single path that
  ///   this `bmct` object executed has been model-checked, you can resume
  ///   exploring further paths by popping an element from
  ///   `branch_worklist` and using it to construct a path_explorert
  ///   object.
  bmct(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv,
    goto_symext::branch_worklistt &_branch_worklist)
    : safety_checkert(ns, _message_handler),
      options(_options),
      outer_symbol_table(outer_symbol_table),
      ns(outer_symbol_table, symex_symbol_table),
      equation(),
      branch_worklist(_branch_worklist),
      symex(_message_handler, outer_symbol_table, equation, branch_worklist),
      prop_conv(_prop_conv),
      ui(ui_message_handlert::uit::PLAIN)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
    symex.record_coverage=
      !options.get_option("symex-coverage-report").empty();
  }

  virtual resultt run(const goto_functionst &goto_functions);
  void setup();
  safety_checkert::resultt execute(const goto_functionst &);
  virtual ~bmct() { }

  // additional stuff
  std::list<exprt> bmc_constraints;

  void set_ui(ui_message_handlert::uit _ui) { ui=_ui; }

  // the safety_checkert interface
  virtual resultt operator()(
    const goto_functionst &goto_functions)
  {
    return run(goto_functions);
  }

  void add_loop_unwind_handler(symex_bmct::loop_unwind_handlert handler)
  {
    symex.add_loop_unwind_handler(handler);
  }

  void add_unwind_recursion_handler(
    symex_bmct::recursion_unwind_handlert handler)
  {
    symex.add_recursion_unwind_handler(handler);
  }

  /// \brief common BMC code, invoked from language-specific frontends
  ///
  /// Do bounded model-checking after all language-specific program
  /// preprocessing has been completed by language-specific frontends.
  /// Language-specific frontends may customize the \ref bmct objects
  /// that are used for model-checking by supplying a function object to
  /// the `frontend_configure_bmc` parameter of this function; the
  /// function object will be called with every \ref bmct object that
  /// is constructed by `do_language_agnostic_bmc`.
  static int do_language_agnostic_bmc(
    const optionst &opts,
    const goto_modelt &goto_model,
    const ui_message_handlert::uit &ui,
    messaget &message,
    std::function<void(bmct &, const goto_modelt &)> frontend_configure_bmc =
      [](bmct &_bmc, const goto_modelt &) { // NOLINT (*)
        // Empty default implementation
      });

protected:
  /// \brief Constructor for path exploration from saved state
  ///
  /// This constructor exists as a delegate for the path_explorert class.
  /// It differs from \ref bmct's public constructor in that it actually
  /// does something with the branch_worklistt argument, and also takes a
  /// symex_target_equationt. See the documentation for path_explorert for
  /// details.
  bmct(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv,
    symex_target_equationt &_equation,
    goto_symext::branch_worklistt &_branch_worklist)
    : safety_checkert(ns, _message_handler),
      options(_options),
      outer_symbol_table(outer_symbol_table),
      ns(outer_symbol_table),
      equation(_equation),
      branch_worklist(_branch_worklist),
      symex(_message_handler, outer_symbol_table, equation, branch_worklist),
      prop_conv(_prop_conv),
      ui(ui_message_handlert::uit::PLAIN)
  {
    symex.constant_propagation = options.get_bool_option("propagation");
    symex.record_coverage =
      !options.get_option("symex-coverage-report").empty();
    INVARIANT(
      options.get_bool_option("paths"),
      "Should only use saved equation & goto_state constructor "
      "when doing path exploration");
  }

  const optionst &options;
  /// \brief symbol table for the goto-program that we will execute
  const symbol_tablet &outer_symbol_table;
  /// \brief symbol table generated during symbolic execution
  symbol_tablet symex_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  goto_symext::branch_worklistt &branch_worklist;
  symex_bmct symex;
  prop_convt &prop_conv;
  std::unique_ptr<memory_model_baset> memory_model;
  // use gui format
  ui_message_handlert::uit ui;

  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);

  virtual resultt decide(
    const goto_functionst &,
    prop_convt &);

  // unwinding
  virtual void setup_unwind();
  virtual void do_unwind_module();
  void do_conversion();

  virtual void freeze_program_variables();

  virtual void show_vcc();
  virtual void show_vcc_plain(std::ostream &out);
  virtual void show_vcc_json(std::ostream &out);

  trace_optionst trace_options()
  {
    return trace_optionst(options);
  }

  virtual resultt all_properties(
    const goto_functionst &goto_functions,
    prop_convt &solver);
  virtual resultt stop_on_fail(
    const goto_functionst &goto_functions,
    prop_convt &solver);
  virtual void show_program();
  virtual void report_success();
  virtual void report_failure();

  virtual void error_trace();
  void output_graphml(
    resultt result,
    const goto_functionst &goto_functions);

  void get_memory_model();
  void slice();
  void show(const goto_functionst &);

  bool cover(
    const goto_functionst &goto_functions,
    const optionst::value_listt &criteria);

  friend class bmc_all_propertiest;
  friend class bmc_covert;
  template <template <class goalt> class covert>
  friend class bmc_goal_covert;
  friend class fault_localizationt;

private:
  /// \brief Class-specific symbolic execution
  ///
  /// This private virtual should be overridden by derived classes to
  /// invoke the symbolic executor in a class-specific way. This
  /// implementation invokes goto_symext::operator() to perform
  /// full-program model-checking from the entry point of the program.
  virtual void
  perform_symbolic_execution(const goto_functionst &goto_functions);
};

/// \brief Symbolic execution from a saved branch point
///
/// Instances of this class execute a single program path from a saved
/// branch point. The saved branch point is supplied to the constructor
/// as a pair of goto_target_equationt (which holds the SSA steps
/// executed so far), and a goto_symex_statet Note that the \ref bmct
/// base class can also execute a single path (it will do so if the
/// `--paths` flag is set in its `options` member), but will always
/// begin symbolic execution from the beginning of the program with
/// fresh state.
class path_explorert : public bmct
{
public:
  path_explorert(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv,
    symex_target_equationt &saved_equation,
    const goto_symex_statet &saved_state,
    goto_symext::branch_worklistt &branch_worklist)
    : bmct(
        _options,
        outer_symbol_table,
        _message_handler,
        _prop_conv,
        saved_equation,
        branch_worklist),
      saved_state(saved_state)
  {
  }

protected:
  const goto_symex_statet &saved_state;

private:
  /// \brief Resume symbolic execution from saved branch point
  ///
  /// This overrides the base implementation to call the symbolic executor with
  /// the saved symex_target_equationt, symbol_tablet, and goto_symex_statet
  /// provided as arguments to the constructor of this class.
  void
  perform_symbolic_execution(const goto_functionst &goto_functions) override;

#define OPT_BMC                                                                \
  "(program-only)"                                                             \
  "(show-loops)"                                                               \
  "(show-vcc)"                                                                 \
  "(slice-formula)"                                                            \
  "(unwinding-assertions)"                                                     \
  "(no-unwinding-assertions)"                                                  \
  "(no-pretty-names)"                                                          \
  "(partial-loops)"                                                            \
  "(paths)"                                                                    \
  "(depth):"                                                                   \
  "(unwind):"                                                                  \
  "(unwindset):"                                                               \
  "(graphml-witness):"                                                         \
  "(unwindset):"

#define HELP_BMC                                                               \
  " --paths                      explore paths one at a time\n"                \
  " --program-only               only show program expression\n"               \
  " --show-loops                 show the loops in the program\n"              \
  " --depth nr                   limit search depth\n"                         \
  " --unwind nr                  unwind nr times\n"                            \
  " --unwindset L:B,...          unwind loop L with a bound of B\n"            \
  "                              (use --show-loops to get the loop IDs)\n"     \
  " --show-vcc                   show the verification conditions\n"           \
  " --slice-formula              remove assignments unrelated to property\n"   \
  " --unwinding-assertions       generate unwinding assertions\n"              \
  " --partial-loops              permit paths with partial loops\n"            \
  " --no-pretty-names            do not simplify identifiers\n"                \
  " --graphml-witness filename   write the witness in GraphML format to "      \
  "filename\n" // NOLINT(*)
};

#endif // CPROVER_CBMC_BMC_H

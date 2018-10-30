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
#include <util/decision_procedure.h>

#include <goto-programs/goto_trace.h>

#include <goto-symex/symex_target_equation.h>
#include <goto-symex/path_storage.h>

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
  ///   up to the unwinding limit. In this case, the `path_storage`
  ///   member shall not be touched; this is enforced by the assertion in
  ///   this class' implementation of bmct::perform_symbolic_execution().
  ///
  /// - If the `--paths` flag is `true`, this `bmct` object will explore a
  ///   single path through the codebase without doing any path merging.
  ///   If some paths were not taken, the state at those branch points
  ///   will be appended to `path_storage`. After the single path that
  ///   this `bmct` object executed has been model-checked, you can resume
  ///   exploring further paths by popping an element from
  ///   `path_storage` and using it to construct a path_explorert
  ///   object.
  bmct(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    ui_message_handlert &_message_handler,
    prop_convt &_prop_conv,
    path_storaget &_path_storage,
    std::function<bool(void)> callback_after_symex)
    : safety_checkert(ns, _message_handler),
      options(_options),
      outer_symbol_table(outer_symbol_table),
      ns(outer_symbol_table, symex_symbol_table),
      equation(),
      path_storage(_path_storage),
      symex(
        _message_handler,
        outer_symbol_table,
        equation,
        options,
        path_storage),
      prop_conv(_prop_conv),
      ui_message_handler(_message_handler),
      driver_callback_after_symex(callback_after_symex)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
    symex.record_coverage=
      !options.get_option("symex-coverage-report").empty();
    symex.self_loops_to_assumptions =
      options.get_bool_option("self-loops-to-assumptions");
  }

  virtual resultt run(const goto_functionst &goto_functions)
  {
    wrapper_goto_modelt model(outer_symbol_table, goto_functions);
    return run(model);
  }
  resultt run(abstract_goto_modelt &);
  void setup();
  safety_checkert::resultt execute(abstract_goto_modelt &);
  virtual ~bmct() { }

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

  static int do_language_agnostic_bmc(
    const path_strategy_choosert &path_strategy_chooser,
    const optionst &opts,
    abstract_goto_modelt &goto_model,
    ui_message_handlert &ui,
    std::function<void(bmct &, const symbol_tablet &)> driver_configure_bmc =
      nullptr,
    std::function<bool(void)> callback_after_symex = nullptr);

protected:
  /// \brief Constructor for path exploration from saved state
  ///
  /// This constructor exists as a delegate for the path_explorert class.
  /// It differs from \ref bmct's public constructor in that it actually
  /// does something with the path_storaget argument, and also takes a
  /// symex_target_equationt. See the documentation for path_explorert for
  /// details.
  bmct(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    ui_message_handlert &_message_handler,
    prop_convt &_prop_conv,
    symex_target_equationt &_equation,
    path_storaget &_path_storage,
    std::function<bool(void)> callback_after_symex)
    : safety_checkert(ns, _message_handler),
      options(_options),
      outer_symbol_table(outer_symbol_table),
      ns(outer_symbol_table),
      equation(_equation),
      path_storage(_path_storage),
      symex(
        _message_handler,
        outer_symbol_table,
        equation,
        options,
        path_storage),
      prop_conv(_prop_conv),
      ui_message_handler(_message_handler),
      driver_callback_after_symex(callback_after_symex)
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
  path_storaget &path_storage;
  symex_bmct symex;
  prop_convt &prop_conv;
  std::unique_ptr<memory_model_baset> memory_model;
  // use gui format
  ui_message_handlert &ui_message_handler;

  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);

  virtual resultt decide(
    const goto_functionst &,
    prop_convt &);

  void do_conversion();

  virtual void freeze_program_variables();

  trace_optionst trace_options()
  {
    return trace_optionst(options);
  }

  virtual resultt all_properties(
    const goto_functionst &goto_functions,
    prop_convt &solver);
  virtual resultt stop_on_fail(prop_convt &solver);
  virtual void report_success();
  virtual void report_failure();

  static void report_success(messaget &, ui_message_handlert &);
  static void report_failure(messaget &, ui_message_handlert &);

  virtual void error_trace();
  void output_graphml(resultt result);

  void get_memory_model();
  void slice();
  void show();

  bool cover(const goto_functionst &goto_functions);

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
  virtual void perform_symbolic_execution(
    goto_symext::get_goto_functiont get_goto_function);

  /// Optional callback, to be run after symex but before handing the resulting
  /// equation to the solver. If it returns true then we will skip the solver
  /// stage and return "safe" (no assertions violated / coverage goals reached),
  /// similar to the behaviour when 'show-vcc' or 'program-only' are specified.
  std::function<bool(void)> driver_callback_after_symex;
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
    ui_message_handlert &_message_handler,
    prop_convt &_prop_conv,
    symex_target_equationt &saved_equation,
    const goto_symex_statet &saved_state,
    path_storaget &path_storage,
    std::function<bool(void)> callback_after_symex)
    : bmct(
        _options,
        outer_symbol_table,
        _message_handler,
        _prop_conv,
        saved_equation,
        path_storage,
        callback_after_symex),
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
  void perform_symbolic_execution(
    goto_symext::get_goto_functiont get_goto_function) override;
};

#define OPT_BMC                                                                \
  "(program-only)"                                                             \
  "(show-loops)"                                                               \
  "(show-vcc)"                                                                 \
  "(slice-formula)"                                                            \
  "(unwinding-assertions)"                                                     \
  "(no-unwinding-assertions)"                                                  \
  "(no-pretty-names)"                                                          \
  "(no-self-loops-to-assumptions)"                                             \
  "(partial-loops)"                                                            \
  "(paths):"                                                                   \
  "(show-symex-strategies)"                                                    \
  "(depth):"                                                                   \
  "(unwind):"                                                                  \
  "(unwindset):"                                                               \
  "(graphml-witness):"                                                         \
  "(unwindset):"

#define HELP_BMC                                                               \
  " --paths [strategy]           explore paths one at a time\n"                \
  " --show-symex-strategies      list strategies for use with --paths\n"       \
  " --program-only               only show program expression\n"               \
  " --show-loops                 show the loops in the program\n"              \
  " --depth nr                   limit search depth\n"                         \
  " --unwind nr                  unwind nr times\n"                            \
  " --unwindset L:B,...          unwind loop L with a bound of B\n"            \
  "                              (use --show-loops to get the loop IDs)\n"     \
  " --show-vcc                   show the verification conditions\n"           \
  " --slice-formula              remove assignments unrelated to property\n"   \
  " --unwinding-assertions       generate unwinding assertions (cannot be\n"   \
  "                              used with --cover or --partial-loops)\n"      \
  " --partial-loops              permit paths with partial loops\n"            \
  " --no-self-loops-to-assumptions\n"                                          \
  "                              do not simplify while(1){} to assume(0)\n"    \
  " --no-pretty-names            do not simplify identifiers\n"                \
  " --graphml-witness filename   write the witness in GraphML format to "      \
  "filename\n" // NOLINT(*)

#endif // CPROVER_CBMC_BMC_H

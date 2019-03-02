/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_H

#include <util/options.h>
#include <util/message.h>

#include <goto-programs/abstract_goto_model.h>

#include "path_storage.h"

class byte_extract_exprt;
class typet;
class code_typet;
class symbol_tablet;
class code_assignt;
class code_function_callt;
class exprt;
class goto_symex_statet;
class guardt;
class if_exprt;
class index_exprt;
class symbol_exprt;
class member_exprt;
class namespacet;
class side_effect_exprt;
class typecast_exprt;

/// Configuration of the symbolic execution
struct symex_configt final
{
  unsigned max_depth;
  bool doing_path_exploration;
  bool allow_pointer_unsoundness;
  bool constant_propagation;
  bool self_loops_to_assumptions;
  bool simplify_opt;
  bool unwinding_assertions;
  bool partial_loops;
  mp_integer debug_level;

  /// \brief Should the additional validation checks be run?
  ///
  /// If this flag is set the checks for renaming (both level1 and level2) are
  /// executed in the goto_symex_statet (in the assignment method).
  bool run_validation_checks;

  explicit symex_configt(const optionst &options);
};

/// \brief The main class for the forward symbolic simulator
///
/// Higher-level architectural information on symbolic execution is
/// documented in the \ref symex-overview
/// "Symbolic execution module page".
class goto_symext
{
public:
  typedef goto_symex_statet statet;

  goto_symext(
    message_handlert &mh,
    const symbol_tablet &outer_symbol_table,
    symex_target_equationt &_target,
    const optionst &options,
    path_storaget &path_storage)
    : should_pause_symex(false),
      symex_config(options),
      language_mode(),
      outer_symbol_table(outer_symbol_table),
      ns(outer_symbol_table),
      target(_target),
      atomic_section_counter(0),
      log(mh),
      path_storage(path_storage),
      path_segment_vccs(0),
      _total_vccs(std::numeric_limits<unsigned>::max()),
      _remaining_vccs(std::numeric_limits<unsigned>::max())
  {
  }

  virtual ~goto_symext() = default;

  typedef
    std::function<const goto_functionst::goto_functiont &(const irep_idt &)>
    get_goto_functiont;

  /// Return a function to get/load a goto function from the given goto model
  static get_goto_functiont get_goto_function(abstract_goto_modelt &);

  /// \brief symex entire program starting from entry point
  ///
  /// The state that goto_symext maintains has a large memory footprint.
  /// This method deallocates the state as soon as symbolic execution
  /// has completed, so use it if you don't care about having the state
  /// around afterwards.
  virtual void symex_from_entry_point_of(
    const get_goto_functiont &get_goto_function,
    symbol_tablet &new_symbol_table);

  /// Puts the initial state of the entry point function into the path storage
  virtual void initialize_path_storage_from_entry_point_of(
    const get_goto_functiont &get_goto_function,
    symbol_tablet &new_symbol_table);

  /// Performs symbolic execution using a state and equation that have
  /// already been used to symex part of the program. The state is not
  /// re-initialized; instead, symbolic execution resumes from the program
  /// counter of the saved state.
  virtual void resume_symex_from_saved_state(
    const get_goto_functiont &get_goto_function,
    const statet &saved_state,
    symex_target_equationt *saved_equation,
    symbol_tablet &new_symbol_table);

  //// \brief symex entire program starting from entry point
  ///
  /// This method uses the `state` argument as the symbolic execution
  /// state, which is useful for examining the state after this method
  /// returns. The state that goto_symext maintains has a large memory
  /// footprint, so if keeping the state around is not necessary,
  /// clients should instead call goto_symext::symex_from_entry_point_of().
  virtual void symex_with_state(
    statet &,
    const get_goto_functiont &,
    symbol_tablet &);

  /// \brief Have states been pushed onto the workqueue?
  ///
  /// If this flag is set at the end of a symbolic execution run, it means that
  /// symex has been paused because we encountered a GOTO instruction while
  /// doing path exploration, and thus pushed the successor states of the GOTO
  /// onto path_storage. The symbolic execution caller should now choose which
  /// successor state to continue executing, and resume symex from that state.
  bool should_pause_symex;

protected:
  const symex_configt symex_config;

  /// Initialize the symbolic execution and the given state with
  /// the beginning of the entry point function.
  /// \param get_goto_function: producer for GOTO functions
  /// \return Initialized symex state.
  std::unique_ptr<statet>
  initialize_entry_point_state(const get_goto_functiont &get_goto_function);

  /// Invokes symex_step and verifies whether additional threads can be
  /// executed.
  /// \param state: Current GOTO symex step.
  /// \param get_goto_function: function that retrieves function bodies
  void symex_threaded_step(
    statet &, const get_goto_functiont &);

  virtual void symex_step(
    const get_goto_functiont &,
    statet &);

public:

  /// language_mode: ID_java, ID_C or another language identifier
  /// if we know the source language in use, irep_idt() otherwise.
  irep_idt language_mode;

protected:

  /// The symbol table associated with the goto-program that we're
  /// executing. This symbol table will not additionally contain objects
  /// that are dynamically created as part of symbolic execution; the
  /// names of those object are stored in the symbol table passed as the
  /// `new_symbol_table` argument to the `symex_*` methods.
  const symbol_tablet &outer_symbol_table;

  /// Initialized just before symbolic execution begins, to point to
  /// both `outer_symbol_table` and the symbol table owned by the
  /// `goto_symex_statet` object used during symbolic execution. That
  /// symbol table must be owned by goto_symex_statet rather than passed
  /// in, in case the state is saved and resumed. This namespacet is
  /// used during symbolic execution to look up names from the original
  /// goto-program, and the names of dynamically-created objects.
  namespacet ns;
  symex_target_equationt &target;
  unsigned atomic_section_counter;

  mutable messaget log;

  friend class symex_dereference_statet;

  // this does the following:
  // a) rename non-det choices
  // b) remove pointer dereferencing
  // c) clean up byte_extract on the lhs of an assignment
  void clean_expr(
    exprt &, statet &, bool write);

  void trigger_auto_object(const exprt &, statet &);
  void initialize_auto_object(const exprt &, statet &);
  void process_array_expr(statet &, exprt &);
  exprt make_auto_object(const typet &, statet &);
  virtual void dereference(exprt &, statet &);

  void dereference_rec(exprt &, statet &);
  exprt address_arithmetic(
    const exprt &,
    statet &,
    bool keep_array);

  virtual void symex_goto(statet &);
  virtual void symex_start_thread(statet &);
  virtual void symex_atomic_begin(statet &);
  virtual void symex_atomic_end(statet &);
  virtual void symex_decl(statet &);
  virtual void symex_decl(statet &, const symbol_exprt &expr);
  virtual void symex_dead(statet &);
  virtual void symex_other(statet &);

  virtual void vcc(
    const exprt &,
    const std::string &msg,
    statet &);

  virtual void symex_assume(statet &, const exprt &cond);

  /// Merge all branches joining at the current program point. Applies
  /// \ref merge_goto for each goto state (each of which corresponds to previous
  /// branch).
  void merge_gotos(statet &);

  /// Merge a single branch, the symbolic state of which is held in \p
  /// goto_state, into the current overall symbolic state. \p goto_state is no
  /// longer expected to be valid afterwards.
  virtual void merge_goto(goto_statet &&goto_state, statet &);

  void phi_function(const goto_statet &goto_state, statet &);

  // determine whether to unwind a loop -- true indicates abort,
  // with false we continue.
  virtual bool should_stop_unwind(
    const symex_targett::sourcet &source,
    const goto_symex_statet::call_stackt &context,
    unsigned unwind);

  virtual void loop_bound_exceeded(statet &, const exprt &guard);

  virtual void no_body(const irep_idt &)
  {
  }

  /// Symbolic execution of a function call.
  /// Only functions that are symbols are supported, see
  /// \ref goto_symext::symex_function_call_symbol
  virtual void symex_function_call(
    const get_goto_functiont &,
    statet &,
    const code_function_callt &);

  virtual void symex_end_of_function(statet &);

  /// Symbolic execution of a call to a function call.
  /// For functions \c CBMC_trace and functions starting with \c __CPROVER_fkt
  /// see \ref goto_symext::symex_trace and
  /// \ref goto_symext::symex_fkt
  /// For non-special functions see
  /// \ref goto_symext::symex_function_call_code
  virtual void symex_function_call_symbol(
    const get_goto_functiont &,
    statet &,
    const code_function_callt &);

  /// Symbolic execution of a function call by inlining.
  /// Records the call in \p target by appending a function call step and:
  ///   - if the body is available create a new frame, assigns the parameters,
  ///    and proceed to executing the code of the function.
  ///   - otherwise assign a nondetministic value to the left-hand-side of the
  ///     call when there is one
  virtual void symex_function_call_code(
    const get_goto_functiont &,
    statet &,
    const code_function_callt &);

  virtual bool get_unwind_recursion(
    const irep_idt &identifier,
    unsigned thread_nr,
    unsigned unwind);

  /// Iterates over \p arguments and assigns them to the parameters, which are
  /// symbols whose name and type are deduced from the type of \p goto_function.
  /// \param function_identifier: name of the function
  /// \param goto_function: function whose parameters we want to assign
  /// \param [out] state: state of the goto program
  /// \param arguments: arguments that are passed to the function
  void parameter_assignments(
    const irep_idt &function_identifier,
    const goto_functionst::goto_functiont &,
    statet &,
    const exprt::operandst &arguments);

  // exceptions
  void symex_throw(statet &);
  void symex_catch(statet &);

  virtual void do_simplify(exprt &);

  void symex_assign(statet &, const code_assignt &);

  // havocs the given object
  void havoc_rec(statet &, const guardt &, const exprt &);

  typedef symex_targett::assignment_typet assignment_typet;

  void symex_assign_rec(
    statet &,
    const exprt &lhs,
    const exprt &full_lhs,
    const exprt &rhs,
    guardt &,
    assignment_typet);
  void symex_assign_symbol(
    statet &,
    const ssa_exprt &lhs,
    const exprt &full_lhs,
    const exprt &rhs,
    guardt &,
    assignment_typet);
  void symex_assign_typecast(
    statet &,
    const typecast_exprt &lhs,
    const exprt &full_lhs,
    const exprt &rhs,
    guardt &,
    assignment_typet);
  void symex_assign_array(
    statet &,
    const index_exprt &lhs,
    const exprt &full_lhs,
    const exprt &rhs,
    guardt &,
    assignment_typet);
  void symex_assign_struct_member(
    statet &,
    const member_exprt &lhs,
    const exprt &full_lhs,
    const exprt &rhs,
    guardt &,
    assignment_typet);
  void symex_assign_if(
    statet &,
    const if_exprt &lhs,
    const exprt &full_lhs,
    const exprt &rhs,
    guardt &,
    assignment_typet);
  void symex_assign_byte_extract(
    statet &,
    const byte_extract_exprt &lhs,
    const exprt &full_lhs,
    const exprt &rhs,
    guardt &,
    assignment_typet);

  /// Store the \p what expression by recursively descending into the operands
  /// of \p lhs until the first operand \c op0 is _nil_: this _nil_ operand
  /// is then replaced with \p what.
  /// \param lhs: Non-symbol pointed-to expression
  /// \param what: The expression to be added to the \p lhs
  /// \return The resulting expression
  static exprt add_to_lhs(const exprt &lhs, const exprt &what);

  virtual void symex_gcc_builtin_va_arg_next(
    statet &, const exprt &lhs, const side_effect_exprt &);
  virtual void symex_allocate(
    statet &, const exprt &lhs, const side_effect_exprt &);
  virtual void symex_cpp_delete(statet &, const codet &);
  virtual void symex_cpp_new(
    statet &, const exprt &lhs, const side_effect_exprt &);
  virtual void symex_fkt(statet &, const code_function_callt &);
  virtual void symex_trace(statet &, const code_function_callt &);
  virtual void symex_printf(statet &, const exprt &rhs);
  virtual void symex_input(statet &, const codet &);
  virtual void symex_output(statet &, const codet &);

  static unsigned dynamic_counter;

  void rewrite_quantifiers(exprt &, statet &);

  path_storaget &path_storage;

public:
  /// \brief Number of VCCs generated during the run of this goto_symext object
  ///
  /// This member is always initialized to `0` upon construction of this object.
  /// It therefore differs from goto_symex_statet::total_vccs, which persists
  /// across the creation of several goto_symext objects. When CBMC is run in
  /// path-exploration mode, the meaning of this member is "the number of VCCs
  /// generated between the last branch point and the current instruction,"
  /// while goto_symex_statet::total_vccs records the total number of VCCs
  /// generated along the entire path from the beginning of the program.
  std::size_t path_segment_vccs;

protected:
  /// @{\name Statistics
  ///
  /// The actual number of total and remaining VCCs should be assigned to
  /// the relevant members of goto_symex_statet. The members below are used to
  /// cache the values from goto_symex_statet after symex has ended, so that
  /// \ref bmct can read those values even after the state has been deallocated.

  unsigned _total_vccs, _remaining_vccs;
  ///@}

public:
  unsigned get_total_vccs()
  {
    INVARIANT(
      _total_vccs != std::numeric_limits<unsigned>::max(),
      "symex_threaded_step should have been executed at least once before "
      "attempting to read total_vccs");
    return _total_vccs;
  }

  unsigned get_remaining_vccs()
  {
    INVARIANT(
      _remaining_vccs != std::numeric_limits<unsigned>::max(),
      "symex_threaded_step should have been executed at least once before "
      "attempting to read remaining_vccs");
    return _remaining_vccs;
  }

  void validate(const validation_modet vm) const
  {
    target.validate(ns, vm);
  }
};

/// Transition to the next instruction, which increments the internal program
/// counter and initializes the loop counter when it detects a loop (or
/// recursion) being entered. 'Next instruction' in this situation refers
/// to the next one in program order, so it ignores things like unconditional
/// GOTOs, and only goes until the end of the current function.
void symex_transition(goto_symext::statet &state);

void symex_transition(
  goto_symext::statet &,
  goto_programt::const_targett to,
  bool is_backwards_goto);

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_H

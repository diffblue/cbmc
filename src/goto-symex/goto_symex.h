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
#include <util/byte_operators.h>

#include <goto-programs/goto_functions.h>

#include "goto_symex_state.h"
#include "symex_target_equation.h"

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

/// \brief The main class for the forward symbolic simulator
///
/// Higher-level architectural information on symbolic execution is
/// documented in the \ref symex-overview
/// "Symbolic execution module page".
class goto_symext
{
public:
  typedef goto_symex_statet statet;

  /// \brief Information saved at a conditional goto to resume execution
  struct branch_pointt
  {
    symex_target_equationt equation;
    statet state;

    explicit branch_pointt(const symex_target_equationt &e, const statet &s)
      : equation(e), state(s, &equation)
    {
    }

    explicit branch_pointt(const branch_pointt &other)
      : equation(other.equation), state(other.state, &equation)
    {
    }
  };

  typedef std::list<branch_pointt> branch_worklistt;

  goto_symext(
    message_handlert &mh,
    const symbol_tablet &outer_symbol_table,
    symex_target_equationt &_target,
    branch_worklistt &branch_worklist)
    : total_vccs(0),
      remaining_vccs(0),
      constant_propagation(true),
      language_mode(),
      outer_symbol_table(outer_symbol_table),
      ns(outer_symbol_table),
      target(_target),
      atomic_section_counter(0),
      log(mh),
      guard_identifier("goto_symex::\\guard"),
      branch_worklist(branch_worklist)
  {
    options.set_option("simplify", true);
    options.set_option("assertions", true);
  }

  virtual ~goto_symext()
  {
  }

  typedef
    std::function<const goto_functionst::goto_functiont &(const irep_idt &)>
    get_goto_functiont;

  /// \brief symex entire program starting from entry point
  ///
  /// The state that goto_symext maintains has a large memory footprint.
  /// This method deallocates the state as soon as symbolic execution
  /// has completed, so use it if you don't care about having the state
  /// around afterwards.
  virtual void symex_from_entry_point_of(
    const goto_functionst &goto_functions,
    symbol_tablet &new_symbol_table);

  /// \brief symex entire program starting from entry point
  ///
  /// The state that goto_symext maintains has a large memory footprint.
  /// This method deallocates the state as soon as symbolic execution
  /// has completed, so use it if you don't care about having the state
  /// around afterwards.
  virtual void symex_from_entry_point_of(
    const get_goto_functiont &get_goto_function,
    symbol_tablet &new_symbol_table);

  /// Performs symbolic execution using a state and equation that have
  /// already been used to symex part of the program. The state is not
  /// re-initialized; instead, symbolic execution resumes from the program
  /// counter of the saved state.
  virtual void resume_symex_from_saved_state(
    const get_goto_functiont &get_goto_function,
    const statet &saved_state,
    symex_target_equationt *const saved_equation,
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
    const goto_functionst &,
    symbol_tablet &);

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

  /// Symexes from the first instruction and the given state, terminating as
  /// soon as the last instruction is reached.  This is useful to explicitly
  /// symex certain ranges of a program, e.g. in an incremental decision
  /// procedure.
  /// \param state Symex state to start with.
  /// \param goto_functions GOTO model to symex.
  /// \param first Entry point in form of a first instruction.
  /// \param limit Final instruction, which itself will not be symexed.
  virtual void symex_instruction_range(
    statet &,
    const goto_functionst &,
    goto_programt::const_targett first,
    goto_programt::const_targett limit);

  /// Symexes from the first instruction and the given state, terminating as
  /// soon as the last instruction is reached.  This is useful to explicitly
  /// symex certain ranges of a program, e.g. in an incremental decision
  /// procedure.
  /// \param state Symex state to start with.
  /// \param get_goto_function retrieves a function body
  /// \param first Entry point in form of a first instruction.
  /// \param limit Final instruction, which itself will not be symexed.
  virtual void symex_instruction_range(
    statet &state,
    const get_goto_functiont &get_goto_function,
    goto_programt::const_targett first,
    goto_programt::const_targett limit);

protected:
  /// Initialise the symbolic execution and the given state with <code>pc</code>
  /// as entry point.
  /// \param state Symex state to initialise.
  /// \param goto_functions GOTO model to symex.
  /// \param pc first instruction to symex
  /// \param limit final instruction, which itself will not
  /// be symexed.
  void initialize_entry_point(
    statet &state,
    const get_goto_functiont &get_goto_function,
    goto_programt::const_targett pc,
    goto_programt::const_targett limit);

  /// Invokes symex_step and verifies whether additional threads can be
  /// executed.
  /// \param state Current GOTO symex step.
  /// \param get_goto_function function that retrieves function bodies
  void symex_threaded_step(
    statet &, const get_goto_functiont &);

  virtual void symex_step(
    const get_goto_functiont &,
    statet &);

public:
  // these bypass the target maps
  virtual void symex_step_goto(statet &, bool taken);

  // statistics
  unsigned total_vccs, remaining_vccs;

  bool constant_propagation;

  optionst options;

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

  void new_name(symbolt &symbol, statet &state);

  // this does the following:
  // a) rename non-det choices
  // b) remove pointer dereferencing
  // c) clean up byte_extract on the lhs of an assignment
  void clean_expr(
    exprt &, statet &, bool write);

  void trigger_auto_object(const exprt &, statet &);
  void initialize_auto_object(const exprt &, statet &);
  void process_array_expr(exprt &);
  exprt make_auto_object(const typet &, statet &);
  virtual void dereference(exprt &, statet &, const bool write);

  void dereference_rec(
    exprt &,
    statet &,
    guardt &,
    const bool write);

  void dereference_rec_address_of(
    exprt &,
    statet &,
    guardt &);

  static bool is_index_member_symbol_if(const exprt &expr);

  exprt address_arithmetic(
    const exprt &,
    statet &,
    guardt &,
    bool keep_array);

  // guards

  irep_idt guard_identifier;

  // symex
  virtual void symex_transition(
    statet &,
    goto_programt::const_targett to,
    bool is_backwards_goto=false);

  virtual void symex_transition(statet &state)
  {
    goto_programt::const_targett next=state.source.pc;
    ++next;
    symex_transition(state, next);
  }

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

  // gotos
  void merge_gotos(statet &);

  virtual void merge_goto(
    const statet::goto_statet &goto_state,
    statet &);

  void merge_value_sets(
    const statet::goto_statet &goto_state,
    statet &dest);

  void phi_function(
    const statet::goto_statet &goto_state,
    statet &);

  // determine whether to unwind a loop -- true indicates abort,
  // with false we continue.
  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    unsigned unwind);

  virtual void loop_bound_exceeded(statet &, const exprt &guard);

  // function calls

  void pop_frame(statet &);
  void return_assignment(statet &);

  virtual void no_body(const irep_idt &identifier)
  {
  }

  virtual void symex_function_call(
    const get_goto_functiont &,
    statet &,
    const code_function_callt &);

  virtual void symex_end_of_function(statet &);

  virtual void symex_function_call_symbol(
    const get_goto_functiont &,
    statet &,
    const code_function_callt &);

  virtual void symex_function_call_code(
    const get_goto_functiont &,
    statet &,
    const code_function_callt &);

  virtual bool get_unwind_recursion(
    const irep_idt &identifier,
    const unsigned thread_nr,
    unsigned unwind);

  void parameter_assignments(
    const irep_idt function_identifier,
    const goto_functionst::goto_functiont &,
    statet &,
    const exprt::operandst &arguments);

  void locality(
    const irep_idt function_identifier,
    statet &,
    const goto_functionst::goto_functiont &);

  void add_end_of_function(
    exprt &code,
    const irep_idt &identifier);

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

  static exprt add_to_lhs(const exprt &lhs, const exprt &what);

  virtual void symex_gcc_builtin_va_arg_next(
    statet &, const exprt &lhs, const side_effect_exprt &);
  virtual void symex_allocate(
    statet &, const exprt &lhs, const side_effect_exprt &);
  virtual void symex_cpp_delete(statet &, const codet &);
  virtual void symex_cpp_new(
    statet &, const exprt &lhs, const side_effect_exprt &);
  virtual void symex_fkt(statet &, const code_function_callt &);
  virtual void symex_macro(statet &, const code_function_callt &);
  virtual void symex_trace(statet &, const code_function_callt &);
  virtual void symex_printf(statet &, const exprt &lhs, const exprt &rhs);
  virtual void symex_input(statet &, const codet &);
  virtual void symex_output(statet &, const codet &);

  static unsigned nondet_count;
  static unsigned dynamic_counter;

  void read(exprt &);
  void replace_nondet(exprt &);
  void rewrite_quantifiers(exprt &, statet &);

  branch_worklistt &branch_worklist;
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_H

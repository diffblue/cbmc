/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Generate Equation using Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_SYMEX_TARGET_H
#define CPROVER_GOTO_SYMEX_SYMEX_TARGET_H

#include <goto-programs/goto_program.h>

class ssa_exprt;
class symbol_exprt;

/// The interface of the target _container_ for symbolic execution to record its
/// symbolic steps into. Presently, \ref symex_target_equationt is the only
/// implementation of this interface.
class symex_targett
{
public:
  symex_targett()
  {
  }

  virtual ~symex_targett() { }

  /// Identifies source in the context of symbolic execution. Thread number
  /// `thread_nr` is zero by default and the program counter `pc` points to the
  /// first instruction of the input GOTO program.
  struct sourcet
  {
    unsigned thread_nr;
    irep_idt function;
    // The program counter is an iterator which indicates where the execution
    // is in its program sequence
    goto_programt::const_targett pc;
    bool is_set;

    sourcet() : thread_nr(0), function(irep_idt()), is_set(false)
    {
    }

    sourcet(const irep_idt &_function, goto_programt::const_targett _pc)
      : thread_nr(0), function(_function), pc(_pc), is_set(true)
    {
    }

    explicit sourcet(
      const irep_idt &_function,
      const goto_programt &_goto_program)
      : thread_nr(0),
        function(_function),
        pc(_goto_program.instructions.begin()),
        is_set(true)
    {
    }
  };

  enum class assignment_typet
  {
    STATE,
    HIDDEN,
    VISIBLE_ACTUAL_PARAMETER,
    HIDDEN_ACTUAL_PARAMETER,
    PHI,
    GUARD,
  };

  /// Read from a shared variable \p ssa_object (which is both the left- and the
  /// right--hand side of assignment): we effectively assign the value stored in
  /// \p ssa_object by another thread to \p ssa_object in the memory scope of
  /// this thread.
  /// \param guard: Precondition for this read event
  /// \param ssa_object: Variable to be read from
  /// \param atomic_section_id: ID of the atomic section in which this read
  ///  takes place (if any)
  /// \param source: Pointer to location in the input GOTO program of this read
  virtual void shared_read(
    const exprt &guard,
    const ssa_exprt &ssa_object,
    unsigned atomic_section_id,
    const sourcet &source) = 0;

  /// Write to a shared variable \p ssa_object: we effectively assign a value
  /// from this thread to be visible by other threads.
  /// \param guard: Precondition for this write event
  /// \param ssa_object: Variable to be written to
  /// \param atomic_section_id: ID of the atomic section in which this write
  ///  takes place (if any)
  /// \param source: Pointer to location in the input GOTO program of this write
  virtual void shared_write(
    const exprt &guard,
    const ssa_exprt &ssa_object,
    unsigned atomic_section_id,
    const sourcet &source) = 0;

  /// Write to a local variable. The `cond_expr` is _lhs==rhs_.
  /// \param guard: Precondition for this read event
  /// \param ssa_lhs: Variable to be written to, must be a symbol (and not nil)
  /// \param ssa_full_lhs: Full left-hand side with symex level annotations
  /// \param original_full_lhs: Full left-hand side without symex level
  ///  annotations
  /// \param ssa_rhs: Right-hand side of the assignment
  /// \param source: Pointer to location in the input GOTO program of this
  ///  assignment
  /// \param assignment_type: To distinguish between different types of
  ///  assignments (some may be hidden for the further analysis)
  virtual void assignment(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const exprt &ssa_full_lhs,
    const exprt &original_full_lhs,
    const exprt &ssa_rhs,
    const sourcet &source,
    assignment_typet assignment_type)=0;

  /// Declare a fresh variable. The `cond_expr` is _lhs==lhs_.
  /// \param guard: Precondition for a declaration of this variable
  /// \param ssa_lhs: Variable to be declared, must be symbol (and not nil)
  /// \param source: Pointer to location in the input GOTO program of this
  ///  declaration
  /// \param assignment_type: To distinguish between different types of
  ///  assignments (some may be hidden for the further analysis)
  virtual void decl(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source,
    assignment_typet assignment_type)=0;

  /// Remove a variable from the scope.
  /// \param guard: Precondition for removal of this variable
  /// \param ssa_lhs: Variable to be removed, must be symbol
  /// \param source: Pointer to location in the input GOTO program of this
  ///  removal
  virtual void dead(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source)=0;

  /// Record a function call.
  /// \param guard: Precondition for calling a function
  /// \param function_identifier: Name of the function
  /// \param ssa_function_arguments: Vector of arguments in SSA form
  /// \param source: To location in the input GOTO program of this
  /// \param hidden: Should this step be recorded as hidden?
  ///  function call
  virtual void function_call(
    const exprt &guard,
    const irep_idt &function_identifier,
    const std::vector<exprt> &ssa_function_arguments,
    const sourcet &source,
    bool hidden) = 0;

  /// Record return from a function.
  /// \param guard: Precondition for returning from a function
  /// \param source: Pointer to location in the input GOTO program of this
  /// \param hidden: Should this step be recorded as hidden?
  ///  function return
  virtual void
  function_return(const exprt &guard, const sourcet &source, bool hidden) = 0;

  /// Record a location.
  /// \param guard: Precondition for reaching this location
  /// \param source: Pointer to location in the input GOTO program to be
  ///  recorded
  virtual void location(
    const exprt &guard,
    const sourcet &source)=0;

  /// Record an output.
  /// \param guard: Precondition for writing to the output
  /// \param source: Pointer to location in the input GOTO program of this
  ///  output
  /// \param output_id: Name of the output
  /// \param args: A list of IO arguments
  virtual void output(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const std::list<exprt> &args)=0;

  /// Record formatted output.
  /// \param guard: Precondition for writing to the output
  /// \param source: Pointer to location in the input GOTO program of this
  ///  output
  /// \param output_id: Name of the output
  /// \param fmt: Formatting string
  /// \param args: A list of IO arguments
  virtual void output_fmt(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const irep_idt &fmt,
    const std::list<exprt> &args)=0;

  /// Record an input.
  /// \param guard: Precondition for reading from the input
  /// \param source: Pointer to location in the input GOTO program of this
  ///  input
  /// \param input_id: Name of the input
  /// \param args: A list of IO arguments
  virtual void input(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &input_id,
    const std::list<exprt> &args)=0;

  /// Record an assumption.
  /// \param guard: Precondition for reaching this assumption
  /// \param cond: Condition this assumption represents
  /// \param source: Pointer to location in the input GOTO program of this
  ///  assumption
  virtual void assumption(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source)=0;

  /// Record an assertion.
  /// \param guard: Precondition for reaching this assertion
  /// \param cond: Condition this assertion represents
  /// \param msg: The message associated with this assertion
  /// \param source: Pointer to location in the input GOTO program of this
  ///  assertion
  virtual void assertion(
    const exprt &guard,
    const exprt &cond,
    const std::string &msg,
    const sourcet &source)=0;

  /// Record a goto instruction.
  /// \param guard: Precondition for reaching this goto instruction
  /// \param cond: Condition under which this goto should be taken
  /// \param source: Pointer to location in the input GOTO program of this
  ///  goto instruction
  virtual void goto_instruction(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source)=0;

  /// Record a _global_ constraint: there is no guard limiting its scope.
  /// \param cond: Condition represented by this constraint
  /// \param msg: The message associated with this constraint
  /// \param source: Pointer to location in the input GOTO program of this
  ///  constraint
  virtual void constraint(
    const exprt &cond,
    const std::string &msg,
    const sourcet &source)=0;

  /// Record spawning a new thread
  /// \param guard: Precondition for reaching spawning a new thread
  /// \param source: Pointer to location in the input GOTO program where a new
  ///  thread is to be spawned
  virtual void spawn(
    const exprt &guard,
    const sourcet &source)=0;

  /// Record creating a memory barrier
  /// \param guard: Precondition for reaching this barrier
  /// \param source: Pointer to location in the input GOTO program where a new
  ///  barrier is created
  virtual void memory_barrier(
    const exprt &guard,
    const sourcet &source)=0;

  /// Record a beginning of an atomic section
  /// \param guard: Precondition for reaching this atomic section
  /// \param atomic_section_id: Identifier for this atomic section
  /// \param source: Pointer to location in the input GOTO program where an
  ///  atomic section begins
  virtual void atomic_begin(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source)=0;

  /// Record ending an atomic section
  /// \param guard: Precondition for reaching the end of this atomic section
  /// \param atomic_section_id: Identifier for this atomic section
  /// \param source: Pointer to location in the input GOTO program where an
  ///  atomic section ends
  virtual void atomic_end(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source)=0;
};

/// Base class comparison operator for symbolic execution targets. Order first
/// by thread numbers and then by program counters.
/// \param a: Left-hand target
/// \param b: Right-hand target
/// \return _True_ if `a` precedes `b`.
bool operator < (
  const symex_targett::sourcet &a,
  const symex_targett::sourcet &b);

#endif // CPROVER_GOTO_SYMEX_SYMEX_TARGET_H

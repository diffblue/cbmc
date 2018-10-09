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

class symex_targett
{
public:
  symex_targett()
  {
  }

  virtual ~symex_targett() { }

  struct sourcet
  {
    unsigned thread_nr;
    irep_idt function;
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

  // read event
  virtual void shared_read(
    const exprt &guard,
    const ssa_exprt &ssa_rhs,
    unsigned atomic_section_id,
    const sourcet &source)=0;

  // write event
  virtual void shared_write(
    const exprt &guard,
    const ssa_exprt &ssa_rhs,
    unsigned atomic_section_id,
    const sourcet &source)=0;

  // write event - lhs must be symbol
  virtual void assignment(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const exprt &ssa_full_lhs,
    const exprt &original_full_lhs,
    const exprt &ssa_rhs,
    const sourcet &source,
    assignment_typet assignment_type)=0;

  // declare fresh variable - lhs must be symbol
  virtual void decl(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source,
    assignment_typet assignment_type)=0;

  // note the death of a variable - lhs must be symbol
  virtual void dead(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source)=0;

  // record a function call
  virtual void function_call(
    const exprt &guard,
    const irep_idt &function_identifier,
    const std::vector<exprt> &ssa_function_arguments,
    const sourcet &source) = 0;

  // record return from a function
  virtual void function_return(
    const exprt &guard,
    const irep_idt &function_identifier,
    const sourcet &source)=0;

  // just record a location
  virtual void location(
    const exprt &guard,
    const sourcet &source)=0;

  // record output
  virtual void output(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const std::list<exprt> &args)=0;

  // record formatted output
  virtual void output_fmt(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const irep_idt &fmt,
    const std::list<exprt> &args)=0;

  // record input
  virtual void input(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &input_id,
    const std::list<exprt> &args)=0;

  // record an assumption
  virtual void assumption(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source)=0;

  // record an assertion
  virtual void assertion(
    const exprt &guard,
    const exprt &cond,
    const std::string &msg,
    const sourcet &source)=0;

  // record a goto
  virtual void goto_instruction(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source)=0;

  // record a constraint
  virtual void constraint(
    const exprt &cond,
    const std::string &msg,
    const sourcet &source)=0;

  // record thread spawn
  virtual void spawn(
    const exprt &guard,
    const sourcet &source)=0;

  // record memory barrier
  virtual void memory_barrier(
    const exprt &guard,
    const sourcet &source)=0;

  // record atomic section
  virtual void atomic_begin(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source)=0;
  virtual void atomic_end(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source)=0;
};

bool operator < (
  const symex_targett::sourcet &a,
  const symex_targett::sourcet &b);

#endif // CPROVER_GOTO_SYMEX_SYMEX_TARGET_H

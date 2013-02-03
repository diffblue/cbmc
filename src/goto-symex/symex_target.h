/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_SYMEX_TARGET_H
#define CPROVER_GOTO_SYMEX_SYMEX_TARGET_H

#include <goto-programs/goto_program.h>

class guardt;
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
    goto_programt::const_targett pc;
    bool is_set;
  
    sourcet():
      thread_nr(0),
      is_set(false)
    {
    }

    explicit sourcet(
      goto_programt::const_targett _pc):
      thread_nr(0),
      pc(_pc),
      is_set(true)
    {
    }

    explicit sourcet(const goto_programt &_goto_program):
      thread_nr(0),
      pc(_goto_program.instructions.begin()),
      is_set(true)
    {
    }
  };
  
  typedef enum { STATE, HIDDEN } assignment_typet;

  // write to a variable - lhs must be symbol
  virtual void assignment(
    const guardt &guard,
    const symbol_exprt &ssa_lhs,
    const symbol_exprt &original_lhs_object,
    const exprt &ssa_full_lhs,
    const exprt &original_full_lhs,
    const exprt &ssa_rhs,
    const sourcet &source,
    assignment_typet assignment_type)=0;

  // declare fresh variable - lhs must be symbol
  virtual void decl(
    const guardt &guard,
    const symbol_exprt &ssa_lhs,
    const symbol_exprt &original_lhs_object,
    const sourcet &source)=0;

  // note the death of a variable - lhs must be symbol
  virtual void dead(
    const guardt &guard,
    const symbol_exprt &ssa_lhs,
    const symbol_exprt &original_lhs_object,
    const sourcet &source)=0;

  // record a function call
  virtual void function_call(
    const guardt &guard,
    const irep_idt &identifier,
    const sourcet &source)=0;

  // record return from a function
  virtual void function_return(
    const guardt &guard,
    const irep_idt &identifier,
    const sourcet &source)=0;

  // just record a location
  virtual void location(
    const guardt &guard,
    const sourcet &source)=0;

  // record output
  virtual void output(
    const guardt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const std::list<exprt> &args)=0;
  
  // record formatted output
  virtual void output_fmt(
    const guardt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const irep_idt &fmt,
    const std::list<exprt> &args)=0;
  
  // record input
  virtual void input(
    const guardt &guard,
    const sourcet &source,
    const irep_idt &input_id,
    const std::list<exprt> &args)=0;
  
  // record an assumption
  virtual void assumption(
    const guardt &guard,
    const exprt &cond,
    const sourcet &source)=0;

  // record an assertion
  virtual void assertion(
    const guardt &guard,
    const exprt &cond,
    const std::string &msg,
    const sourcet &source)=0;
};

bool operator < (
  const symex_targett::sourcet &a,
  const symex_targett::sourcet &b);

#endif

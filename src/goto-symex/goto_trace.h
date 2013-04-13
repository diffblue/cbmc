/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: July 2005

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_GOTO_TRACE_H
#define CPROVER_GOTO_SYMEX_GOTO_TRACE_H

/*! \file goto-symex/goto_trace.h
 * \brief Traces through goto programs
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include <ostream>
#include <vector>

#include <util/std_expr.h>

#include <goto-programs/goto_program.h>

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_trace_stept 
{
public:
  unsigned step_nr;
  
  bool is_assignment() const      { return type==ASSIGNMENT; }
  bool is_assume() const          { return type==ASSUME; }
  bool is_assert() const          { return type==ASSERT; }
  bool is_constraint() const      { return type==CONSTRAINT; }
  bool is_function_call() const   { return type==FUNCTION_CALL; }
  bool is_function_return() const { return type==FUNCTION_RETURN; }
  bool is_location() const        { return type==LOCATION; }
  bool is_output() const          { return type==OUTPUT; }
  bool is_input() const           { return type==INPUT; }
  bool is_decl() const            { return type==DECL; }
  bool is_dead() const            { return type==DEAD; }
  bool is_shared_read() const     { return type==SHARED_READ; }
  bool is_shared_write() const    { return type==SHARED_WRITE; }
  bool is_spawn() const           { return type==SPAWN; }
  bool is_atomic_begin() const    { return type==ATOMIC_BEGIN; }
  bool is_atomic_end() const      { return type==ATOMIC_END; }

  typedef enum { NONE, ASSIGNMENT, ASSUME, ASSERT,
                 LOCATION, INPUT, OUTPUT, DECL, DEAD,
                 FUNCTION_CALL, FUNCTION_RETURN,
                 CONSTRAINT,
                 SHARED_READ, SHARED_WRITE,
                 SPAWN, ATOMIC_BEGIN, ATOMIC_END } typet;
  typet type;
    
  goto_programt::const_targett pc;

  // this transition done by given thread number
  unsigned thread_nr;
  
  // for assume, assert
  bool cond_value;
  exprt cond_expr;
  
  // for goto
  bool goto_taken;
  
  // for assert
  std::string comment;

  // the object being assigned
  symbol_exprt lhs_object;
  
  // the full, original lhs expression
  exprt full_lhs;

  // A constant with the new value
  exprt lhs_object_value, full_lhs_value;
  
  // for INPUT/OUTPUT
  irep_idt format_string, io_id;
  typedef std::list<exprt> io_argst;
  io_argst io_args;
  bool formatted;
  
  // for function call/return
  irep_idt identifier;

  /*! \brief outputs the trace step in ASCII to a given stream
  */
  void output(
    const class namespacet &ns,
    std::ostream &out) const;
    
  goto_trace_stept():
    step_nr(0),
    type(NONE),
    thread_nr(0),
    cond_value(false),
    formatted(false)
  {
    lhs_object.make_nil();
    lhs_object_value.make_nil();
    full_lhs.make_nil();
    full_lhs_value.make_nil();
    cond_expr.make_nil();
  }
};

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_tracet
{
public:
  typedef std::list<goto_trace_stept> stepst;
  stepst steps;
  
  irep_idt mode;
  
  inline void clear()
  {
    mode.clear();
    steps.clear();
  }
  
  /*! \brief outputs the trace in ASCII to a given stream
  */
  void output(
    const class namespacet &ns,
    std::ostream &out) const;

  inline void swap(goto_tracet &other)
  {
    other.steps.swap(steps);
    other.mode.swap(mode);
  }
  
  inline void add_step(const goto_trace_stept &step)
  {
    steps.push_back(step);
  }
};

void show_goto_trace(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace);

void counterexample_value(
  std::ostream &out,
  const namespacet &ns,
  const symbol_exprt &lhs_object,
  const exprt &full_lhs,
  const exprt &value);

#endif

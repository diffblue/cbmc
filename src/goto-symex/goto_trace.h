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

#include <iostream>
#include <vector>

#include <std_expr.h>

#include <goto-programs/goto_program.h>

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_trace_stept 
{
public:
  unsigned step_nr;
  
  bool is_assignment() const { return type==ASSIGNMENT; }
  bool is_assume() const     { return type==ASSUME; }
  bool is_assert() const     { return type==ASSERT; }
  bool is_location() const   { return type==LOCATION; }
  bool is_output() const     { return type==OUTPUT; }
  bool is_input() const      { return type==INPUT; }

  typedef enum { NONE, ASSIGNMENT, ASSUME, ASSERT,
                 LOCATION, INPUT, OUTPUT } typet;
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

  // A constant with the new value of the object
  exprt lhs_object_value;
  
  // for INPUT/OUTPUT
  irep_idt format_string, io_id;
  typedef std::list<exprt> io_argst;
  io_argst io_args;
  bool formatted;

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
  
  std::string mode;
  
  inline void clear()
  {
    mode.clear();
    steps.clear();
  }
  
  void output(
    const class namespacet &ns,
    std::ostream &out) const;

  inline void swap(goto_tracet &other)
  {
    other.steps.swap(steps);
    other.mode.swap(mode);
  }
};

void show_goto_trace_gui(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace);

void show_goto_trace(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace);

void counterexample_value(
  std::ostream &out,
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &value);

std::string counterexample_value_binary(
  const exprt &expr,
  const namespacet &ns);

#endif

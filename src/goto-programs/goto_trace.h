/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_TRACE_H
#define CPROVER_GOTO_PROGRAMS_GOTO_TRACE_H

/*! \file goto-symex/goto_trace.h
 * \brief Traces through goto programs
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include <iosfwd>
#include <vector>

#include <util/namespace.h>
#include <util/ssa_expr.h>

#include <goto-programs/goto_program.h>
#include <util/make_unique.h>

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_trace_stept
{
public:
  std::size_t step_nr;

  bool is_assignment() const;
  bool is_assume() const;
  bool is_assert() const;
  bool is_goto() const;
  bool is_constraint() const;
  bool is_function_call() const;
  bool is_function_return() const;
  bool is_location() const;
  bool is_output() const;
  bool is_input() const;
  bool is_decl() const;
  bool is_dead() const;
  bool is_shared_read() const;
  bool is_shared_write() const;
  bool is_spawn() const;
  bool is_memory_barrier() const;
  bool is_atomic_begin() const;
  bool is_atomic_end() const;

  enum class typet
  {
    NONE,
    ASSIGNMENT,
    ASSUME,
    ASSERT,
    GOTO,
    LOCATION,
    INPUT,
    OUTPUT,
    DECL,
    DEAD,
    FUNCTION_CALL,
    FUNCTION_RETURN,
    CONSTRAINT,
    SHARED_READ,
    SHARED_WRITE,
    SPAWN,
    MEMORY_BARRIER,
    ATOMIC_BEGIN,
    ATOMIC_END
  };

  // we may choose to hide a step
  bool hidden;

  // this is related to an internal expression
  bool internal;

  // we categorize
  enum class assignment_typet { STATE, ACTUAL_PARAMETER };
  assignment_typet assignment_type;

  goto_programt::const_targett pc;

  // this transition done by given thread number
  unsigned thread_nr;

  // for assume, assert, goto
  bool cond_value;
  exprt cond_expr;

  // for assert
  std::string comment;

  // the object being assigned
  ssa_exprt lhs_object;

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

  virtual typet type() const = 0;

protected:
  goto_trace_stept():
    step_nr(0),
    hidden(false),
    internal(false),
    assignment_type(assignment_typet::STATE),
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

class trace_assignmentt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::ASSIGNMENT; }
};

class trace_assumet : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::ASSUME; }
};

class trace_assertt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::ASSERT; }
};

class trace_gotot : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::GOTO; }
};

class trace_locationt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::LOCATION; }
};

class trace_inputt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::INPUT; }
};

class trace_outputt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::OUTPUT; }
};

class trace_declt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::DECL; }
};

class trace_deadt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::DEAD; }
};

class trace_function_callt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::FUNCTION_CALL; }
};

class trace_function_returnt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::FUNCTION_RETURN; }
};

class trace_constraintt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::CONSTRAINT; }
};

class trace_shared_readt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::SHARED_READ; }
};

class trace_shared_writet : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::SHARED_WRITE; }
};

class trace_spawnt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::SPAWN; }
};

class trace_memory_barriert : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::MEMORY_BARRIER; }
};

class trace_atomic_begint : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::ATOMIC_BEGIN; }
};

class trace_atomic_endt : public goto_trace_stept {
public:
  typet type() const override
  { return goto_trace_stept::typet::ATOMIC_END; }
};

inline std::unique_ptr<goto_trace_stept> make_goto_trace_step(
  goto_trace_stept::typet type)
{
  if (type==goto_trace_stept::typet::ASSIGNMENT)
    return util_make_unique<trace_assignmentt>();
  if (type==goto_trace_stept::typet::ASSUME)
    return util_make_unique<trace_assumet>();
  if (type==goto_trace_stept::typet::ASSERT)
    return util_make_unique<trace_assertt>();
  if (type==goto_trace_stept::typet::GOTO)
    return util_make_unique<trace_gotot>();
  if (type==goto_trace_stept::typet::LOCATION)
    return util_make_unique<trace_locationt>();
  if (type==goto_trace_stept::typet::INPUT)
    return util_make_unique<trace_inputt>();
  if (type==goto_trace_stept::typet::OUTPUT)
    return util_make_unique<trace_outputt>();
  if (type==goto_trace_stept::typet::DECL)
    return util_make_unique<trace_declt>();
  if (type==goto_trace_stept::typet::DEAD)
    return util_make_unique<trace_deadt>();
  if (type==goto_trace_stept::typet::FUNCTION_CALL)
    return util_make_unique<trace_function_callt>();
  if (type==goto_trace_stept::typet::FUNCTION_RETURN)
    return util_make_unique<trace_function_returnt>();
  if (type==goto_trace_stept::typet::CONSTRAINT)
    return util_make_unique<trace_constraintt>();
  if (type==goto_trace_stept::typet::SHARED_READ)
    return util_make_unique<trace_shared_readt>();
  if (type==goto_trace_stept::typet::SHARED_WRITE)
    return util_make_unique<trace_shared_writet>();
  if (type==goto_trace_stept::typet::SPAWN)
    return util_make_unique<trace_spawnt>();
  if (type==goto_trace_stept::typet::MEMORY_BARRIER)
    return util_make_unique<trace_memory_barriert>();
  if (type==goto_trace_stept::typet::ATOMIC_BEGIN)
    return util_make_unique<trace_atomic_begint>();
  if (type==goto_trace_stept::typet::ATOMIC_END)
    return util_make_unique<trace_atomic_endt>();
  UNREACHABLE;
}

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_tracet
{
public:
  typedef std::list<std::unique_ptr<goto_trace_stept>> stepst;
  stepst steps;

  irep_idt mode;

  void clear()
  {
    mode.clear();
    steps.clear();
  }

  /*! \brief outputs the trace in ASCII to a given stream
  */
  void output(
    const class namespacet &ns,
    std::ostream &out) const;

  void swap(goto_tracet &other)
  {
    other.steps.swap(steps);
    other.mode.swap(mode);
  }

  void add_step(std::unique_ptr<goto_trace_stept> step)
  {
    steps.push_back(std::move(step));
  }

  // retrieves the final step in the trace for manipulation
  // (used to fill a trace from code, hence non-const)
  inline goto_trace_stept &get_last_step()
  {
    return *steps.back();
  }

  // delete all steps after (not including) s
  void trim_after(stepst::iterator s)
  {
    assert(s!=steps.end());
    steps.erase(++s, steps.end());
  }
};

void show_goto_trace(
  std::ostream &out,
  const namespacet &,
  const goto_tracet &);

void trace_value(
  std::ostream &out,
  const namespacet &,
  const ssa_exprt &lhs_object,
  const exprt &full_lhs,
  const exprt &value);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_TRACE_H

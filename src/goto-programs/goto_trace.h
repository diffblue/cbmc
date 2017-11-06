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
#include <util/visitor_generator.h>

#include <goto-programs/goto_program.h>
#include <util/make_unique.h>

class trace_assignmentt;
class trace_assumet;
class trace_assertt;
class trace_gotot;
class trace_locationt;
class trace_inputt;
class trace_outputt;
class trace_declt;
class trace_deadt;
class trace_function_callt;
class trace_function_returnt;
class trace_constraintt;
class trace_shared_readt;
class trace_shared_writet;
class trace_spawnt;
class trace_memory_barriert;
class trace_atomic_begint;
class trace_atomic_endt;

namespace detail
{
using trace_step_ref_typest = typelistt<trace_assignmentt &,
                                        trace_assumet &,
                                        trace_assertt &,
                                        trace_gotot &,
                                        trace_locationt &,
                                        trace_inputt &,
                                        trace_outputt &,
                                        trace_declt &,
                                        trace_deadt &,
                                        trace_function_callt &,
                                        trace_function_returnt &,
                                        trace_constraintt &,
                                        trace_shared_readt &,
                                        trace_shared_writet &,
                                        trace_spawnt &,
                                        trace_memory_barriert &,
                                        trace_atomic_begint &,
                                        trace_atomic_endt &>;

using trace_step_const_ref_typest = typelistt<const trace_assignmentt &,
                                              const trace_assumet &,
                                              const trace_assertt &,
                                              const trace_gotot &,
                                              const trace_locationt &,
                                              const trace_inputt &,
                                              const trace_outputt &,
                                              const trace_declt &,
                                              const trace_deadt &,
                                              const trace_function_callt &,
                                              const trace_function_returnt &,
                                              const trace_constraintt &,
                                              const trace_shared_readt &,
                                              const trace_shared_writet &,
                                              const trace_spawnt &,
                                              const trace_memory_barriert &,
                                              const trace_atomic_begint &,
                                              const trace_atomic_endt &>;

} // namespace detail

using trace_visitor_const_argst =
  visitor_generatort<detail::trace_step_const_ref_typest>;
using trace_const_visitor_const_argst =
  const_visitor_generatort<detail::trace_step_const_ref_typest>;
using trace_visitor = visitor_generatort<detail::trace_step_ref_typest>;
using trace_const_visitor =
  const_visitor_generatort<detail::trace_step_ref_typest>;

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

  virtual void accept(trace_visitor_const_argst &v) const = 0;
  virtual void accept(const trace_const_visitor_const_argst &v) const = 0;
  virtual void accept(trace_visitor &v) = 0;
  virtual void accept(const trace_const_visitor &v) = 0;

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

private:
  virtual std::string name() const = 0;
  virtual std::string formatted_cond_value() const { return ""; }
};

template <typename T>
class goto_trace_accept_mixint : public goto_trace_stept {
public:
  void accept(trace_visitor_const_argst &v) const override
  {
    v.visit(get_base());
  }
  void accept(const trace_const_visitor_const_argst &v) const override
  {
    v.visit(get_base());
  }
  void accept(trace_visitor &v) override
  {
    v.visit(get_base());
  }
  void accept(const trace_const_visitor &v) override
  {
    v.visit(get_base());
  }

private:
  T &get_base()
  {
    return static_cast<T &>(*this);
  }

  const T &get_base() const
  {
    return static_cast<const T &>(*this);
  }

};

class trace_assignmentt : public goto_trace_accept_mixint<trace_assignmentt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::ASSIGNMENT; }

private:
  std::string name() const override { return "ASSIGNMENT"; }
};

class trace_assumet : public goto_trace_accept_mixint<trace_assumet>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::ASSUME; }

private:
  std::string name() const override { return "ASSUME"; }
  std::string formatted_cond_value() const override
  {
    std::ostringstream ss;
    ss << " (" << cond_value << ')';
    return ss.str();
  }
};

class trace_assertt : public goto_trace_accept_mixint<trace_assertt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::ASSERT; }

private:
  std::string name() const override { return "ASSERT"; }
  std::string formatted_cond_value() const override
  {
    std::ostringstream ss;
    ss << " (" << cond_value << ')';
    return ss.str();
  }
};

class trace_gotot : public goto_trace_accept_mixint<trace_gotot>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::GOTO; }

private:
  std::string name() const override { return "GOTO"; }
  std::string formatted_cond_value() const override
  {
    std::ostringstream ss;
    ss << " (" << cond_value << ')';
    return ss.str();
  }
};

class trace_locationt : public goto_trace_accept_mixint<trace_locationt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::LOCATION; }

private:
  std::string name() const override { return "LOCATION"; }
};

class trace_inputt : public goto_trace_accept_mixint<trace_inputt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::INPUT; }

private:
  std::string name() const override { return "INPUT"; }
};

class trace_outputt : public goto_trace_accept_mixint<trace_outputt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::OUTPUT; }

private:
  std::string name() const override { return "OUTPUT"; }
};

class trace_declt : public goto_trace_accept_mixint<trace_declt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::DECL; }

private:
  std::string name() const override { return "DECL"; }
};

class trace_deadt : public goto_trace_accept_mixint<trace_deadt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::DEAD; }

private:
  std::string name() const override { return "DEAD"; }
};

class trace_function_callt
  : public goto_trace_accept_mixint<trace_function_callt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::FUNCTION_CALL; }

private:
  std::string name() const override { return "FUNCTION CALL"; }
};

class trace_function_returnt
  : public goto_trace_accept_mixint<trace_function_returnt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::FUNCTION_RETURN; }

private:
  std::string name() const override { return "FUNCTION RETURN"; }
};

class trace_constraintt : public goto_trace_accept_mixint<trace_constraintt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::CONSTRAINT; }

private:
  std::string name() const override { return "CONSTRAINT"; }
};

class trace_shared_readt : public goto_trace_accept_mixint<trace_shared_readt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::SHARED_READ; }

private:
  std::string name() const override { return "SHARED READ"; }
};

class trace_shared_writet : public goto_trace_accept_mixint<trace_shared_writet>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::SHARED_WRITE; }

private:
  std::string name() const override { return "SHARED WRITE"; }
};

class trace_spawnt : public goto_trace_accept_mixint<trace_spawnt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::SPAWN; }

private:
  std::string name() const override { return "SPAWN"; }
};

class trace_memory_barriert
  : public goto_trace_accept_mixint<trace_memory_barriert>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::MEMORY_BARRIER; }

private:
  std::string name() const override { return "MEMORY BARRIER"; }
};

class trace_atomic_begint : public goto_trace_accept_mixint<trace_atomic_begint>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::ATOMIC_BEGIN; }

private:
  std::string name() const override { return "ATOMIC BEGIN"; }
};

class trace_atomic_endt : public goto_trace_accept_mixint<trace_atomic_endt>
{
public:
  typet type() const override
  { return goto_trace_stept::typet::ATOMIC_END; }

private:
  std::string name() const override { return "ATOMIC END"; }
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

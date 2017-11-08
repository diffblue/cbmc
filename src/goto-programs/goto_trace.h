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

class trace_visitor_const_argst
{
public:
  virtual ~trace_visitor_const_argst() = default;

  virtual void visit(const trace_assignmentt &) = 0;
  virtual void visit(const trace_assumet &) = 0;
  virtual void visit(const trace_assertt &) = 0;
  virtual void visit(const trace_gotot &) = 0;
  virtual void visit(const trace_locationt &) = 0;
  virtual void visit(const trace_inputt &) = 0;
  virtual void visit(const trace_outputt &) = 0;
  virtual void visit(const trace_declt &) = 0;
  virtual void visit(const trace_deadt &) = 0;
  virtual void visit(const trace_function_callt &) = 0;
  virtual void visit(const trace_function_returnt &) = 0;
  virtual void visit(const trace_constraintt &) = 0;
  virtual void visit(const trace_shared_readt &) = 0;
  virtual void visit(const trace_shared_writet &) = 0;
  virtual void visit(const trace_spawnt &) = 0;
  virtual void visit(const trace_memory_barriert &) = 0;
  virtual void visit(const trace_atomic_begint &) = 0;
  virtual void visit(const trace_atomic_endt &) = 0;
};

class trace_const_visitor_const_argst
{
public:
  virtual ~trace_const_visitor_const_argst() = default;

  virtual void visit(const trace_assignmentt &) const = 0;
  virtual void visit(const trace_assumet &) const = 0;
  virtual void visit(const trace_assertt &) const = 0;
  virtual void visit(const trace_gotot &) const = 0;
  virtual void visit(const trace_locationt &) const = 0;
  virtual void visit(const trace_inputt &) const = 0;
  virtual void visit(const trace_outputt &) const = 0;
  virtual void visit(const trace_declt &) const = 0;
  virtual void visit(const trace_deadt &) const = 0;
  virtual void visit(const trace_function_callt &) const = 0;
  virtual void visit(const trace_function_returnt &) const = 0;
  virtual void visit(const trace_constraintt &) const = 0;
  virtual void visit(const trace_shared_readt &) const = 0;
  virtual void visit(const trace_shared_writet &) const = 0;
  virtual void visit(const trace_spawnt &) const = 0;
  virtual void visit(const trace_memory_barriert &) const = 0;
  virtual void visit(const trace_atomic_begint &) const = 0;
  virtual void visit(const trace_atomic_endt &) const = 0;
};

class trace_visitort
{
public:
  virtual ~trace_visitort() = default;

  virtual void visit(trace_assignmentt &) = 0;
  virtual void visit(trace_assumet &) = 0;
  virtual void visit(trace_assertt &) = 0;
  virtual void visit(trace_gotot &) = 0;
  virtual void visit(trace_locationt &) = 0;
  virtual void visit(trace_inputt &) = 0;
  virtual void visit(trace_outputt &) = 0;
  virtual void visit(trace_declt &) = 0;
  virtual void visit(trace_deadt &) = 0;
  virtual void visit(trace_function_callt &) = 0;
  virtual void visit(trace_function_returnt &) = 0;
  virtual void visit(trace_constraintt &) = 0;
  virtual void visit(trace_shared_readt &) = 0;
  virtual void visit(trace_shared_writet &) = 0;
  virtual void visit(trace_spawnt &) = 0;
  virtual void visit(trace_memory_barriert &) = 0;
  virtual void visit(trace_atomic_begint &) = 0;
  virtual void visit(trace_atomic_endt &) = 0;
};

class trace_const_visitort
{
public:
  virtual ~trace_const_visitort() = default;

  virtual void visit(trace_assignmentt &) const = 0;
  virtual void visit(trace_assumet &) const = 0;
  virtual void visit(trace_assertt &) const = 0;
  virtual void visit(trace_gotot &) const = 0;
  virtual void visit(trace_locationt &) const = 0;
  virtual void visit(trace_inputt &) const = 0;
  virtual void visit(trace_outputt &) const = 0;
  virtual void visit(trace_declt &) const = 0;
  virtual void visit(trace_deadt &) const = 0;
  virtual void visit(trace_function_callt &) const = 0;
  virtual void visit(trace_function_returnt &) const = 0;
  virtual void visit(trace_constraintt &) const = 0;
  virtual void visit(trace_shared_readt &) const = 0;
  virtual void visit(trace_shared_writet &) const = 0;
  virtual void visit(trace_spawnt &) const = 0;
  virtual void visit(trace_memory_barriert &) const = 0;
  virtual void visit(trace_atomic_begint &) const = 0;
  virtual void visit(trace_atomic_endt &) const = 0;
};

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_trace_stept
{
public:
  std::size_t step_nr;

  virtual bool is_assignment() const
  {
    return false;
  }
  virtual bool is_assume() const
  {
    return false;
  }
  virtual bool is_assert() const
  {
    return false;
  }
  virtual bool is_goto() const
  {
    return false;
  }
  virtual bool is_constraint() const
  {
    return false;
  }
  virtual bool is_function_call() const
  {
    return false;
  }
  virtual bool is_function_return() const
  {
    return false;
  }
  virtual bool is_location() const
  {
    return false;
  }
  virtual bool is_output() const
  {
    return false;
  }
  virtual bool is_input() const
  {
    return false;
  }
  virtual bool is_decl() const
  {
    return false;
  }
  virtual bool is_dead() const
  {
    return false;
  }
  virtual bool is_shared_read() const
  {
    return false;
  }
  virtual bool is_shared_write() const
  {
    return false;
  }
  virtual bool is_spawn() const
  {
    return false;
  }
  virtual bool is_memory_barrier() const
  {
    return false;
  }
  virtual bool is_atomic_begin() const
  {
    return false;
  }
  virtual bool is_atomic_end() const
  {
    return false;
  }

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

  virtual void accept(trace_visitor_const_argst &v) const = 0;
  virtual void accept(const trace_const_visitor_const_argst &v) const = 0;
  virtual void accept(trace_visitort &v) = 0;
  virtual void accept(const trace_const_visitort &v) = 0;

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
  void accept(trace_visitort &v) override
  {
    v.visit(get_base());
  }
  void accept(const trace_const_visitort &v) override
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
  bool is_assignment() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "ASSIGNMENT";
  }
};

class trace_assumet : public goto_trace_accept_mixint<trace_assumet>
{
public:
  bool is_assume() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "ASSUME";
  }
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
  bool is_assert() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "ASSERT";
  }
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
  bool is_goto() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "GOTO";
  }
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
  bool is_location() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "LOCATION";
  }
};

class trace_inputt : public goto_trace_accept_mixint<trace_inputt>
{
public:
  bool is_input() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "INPUT";
  }
};

class trace_outputt : public goto_trace_accept_mixint<trace_outputt>
{
public:
  bool is_output() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "OUTPUT";
  }
};

class trace_declt : public goto_trace_accept_mixint<trace_declt>
{
public:
  bool is_decl() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "DECL";
  }
};

class trace_deadt : public goto_trace_accept_mixint<trace_deadt>
{
public:
  bool is_dead() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "DEAD";
  }
};

class trace_function_callt
  : public goto_trace_accept_mixint<trace_function_callt>
{
public:
  bool is_function_call() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "FUNCTION CALL";
  }
};

class trace_function_returnt
  : public goto_trace_accept_mixint<trace_function_returnt>
{
public:
  bool is_function_return() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "FUNCTION RETURN";
  }
};

class trace_constraintt : public goto_trace_accept_mixint<trace_constraintt>
{
public:
  bool is_constraint() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "CONSTRAINT";
  }
};

class trace_shared_readt : public goto_trace_accept_mixint<trace_shared_readt>
{
public:
  bool is_shared_read() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "SHARED READ";
  }
};

class trace_shared_writet : public goto_trace_accept_mixint<trace_shared_writet>
{
public:
  bool is_shared_write() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "SHARED WRITE";
  }
};

class trace_spawnt : public goto_trace_accept_mixint<trace_spawnt>
{
public:
  bool is_spawn() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "SPAWN";
  }
};

class trace_memory_barriert
  : public goto_trace_accept_mixint<trace_memory_barriert>
{
public:
  bool is_memory_barrier() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "MEMORY BARRIER";
  }
};

class trace_atomic_begint : public goto_trace_accept_mixint<trace_atomic_begint>
{
public:
  bool is_atomic_begin() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "ATOMIC BEGIN";
  }
};

class trace_atomic_endt : public goto_trace_accept_mixint<trace_atomic_endt>
{
public:
  bool is_atomic_end() const override
  {
    return true;
  }

private:
  std::string name() const override
  {
    return "ATOMIC END";
  }
};

class defaulted_trace_const_visitor_const_argst
  : public trace_const_visitor_const_argst
{
public:
  virtual void default_visit(const goto_trace_stept &) const = 0;

  void visit(const trace_assignmentt &x) const override { default_visit(x); }
  void visit(const trace_assumet &x) const override { default_visit(x); }
  void visit(const trace_assertt &x) const override { default_visit(x); }
  void visit(const trace_gotot &x) const override { default_visit(x); }
  void visit(const trace_locationt &x) const override { default_visit(x); }
  void visit(const trace_inputt &x) const override { default_visit(x); }
  void visit(const trace_outputt &x) const override { default_visit(x); }
  void visit(const trace_declt &x) const override { default_visit(x); }
  void visit(const trace_deadt &x) const override { default_visit(x); }
  void visit(const trace_function_callt &x) const override { default_visit(x); }
  void visit(const trace_function_returnt &x) const override { default_visit(x); }
  void visit(const trace_constraintt &x) const override { default_visit(x); }
  void visit(const trace_shared_readt &x) const override { default_visit(x); }
  void visit(const trace_shared_writet &x) const override { default_visit(x); }
  void visit(const trace_spawnt &x) const override { default_visit(x); }
  void visit(const trace_memory_barriert &x) const override { default_visit(x); }
  void visit(const trace_atomic_begint &x) const override { default_visit(x); }
  void visit(const trace_atomic_endt &x) const override { default_visit(x); }
};

class defaulted_trace_const_visitort : public trace_const_visitort
{
public:
  virtual void default_visit(goto_trace_stept &) const = 0;

  void visit( trace_assignmentt &x) const override { default_visit(x); }
  void visit( trace_assumet &x) const override { default_visit(x); }
  void visit( trace_assertt &x) const override { default_visit(x); }
  void visit( trace_gotot &x) const override { default_visit(x); }
  void visit( trace_locationt &x) const override { default_visit(x); }
  void visit( trace_inputt &x) const override { default_visit(x); }
  void visit( trace_outputt &x) const override { default_visit(x); }
  void visit( trace_declt &x) const override { default_visit(x); }
  void visit( trace_deadt &x) const override { default_visit(x); }
  void visit( trace_function_callt &x) const override { default_visit(x); }
  void visit( trace_function_returnt &x) const override { default_visit(x); }
  void visit( trace_constraintt &x) const override { default_visit(x); }
  void visit( trace_shared_readt &x) const override { default_visit(x); }
  void visit( trace_shared_writet &x) const override { default_visit(x); }
  void visit( trace_spawnt &x) const override { default_visit(x); }
  void visit( trace_memory_barriert &x) const override { default_visit(x); }
  void visit( trace_atomic_begint &x) const override { default_visit(x); }
  void visit( trace_atomic_endt &x) const override { default_visit(x); }
};

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

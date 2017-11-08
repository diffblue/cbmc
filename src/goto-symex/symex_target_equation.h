/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Generate Equation using Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_SYMEX_TARGET_EQUATION_H
#define CPROVER_GOTO_SYMEX_SYMEX_TARGET_EQUATION_H

#include <list>
#include <iosfwd>

#include <util/merge_irep.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_trace.h>

#include <solvers/prop/literal.h>

#include "symex_target.h"

class decision_proceduret;
class namespacet;
class prop_convt;

class SSA_assertt;
class SSA_assignmentt;
class SSA_assumet;
class SSA_atomic_begint;
class SSA_atomic_endt;
class SSA_constraintt;
class SSA_declt;
class SSA_deadt;
class SSA_function_callt;
class SSA_function_returnt;
class SSA_gotot;
class SSA_inputt;
class SSA_locationt;
class SSA_memory_barriert;
class SSA_outputt;
class SSA_shared_readt;
class SSA_shared_writet;
class SSA_spawnt;

class SSA_visitor_const_argst
{
public:
  virtual ~SSA_visitor_const_argst() = default;

  virtual void visit(const SSA_assertt &) = 0;
  virtual void visit(const SSA_assumet &) = 0;
  virtual void visit(const SSA_assignmentt &) = 0;
  virtual void visit(const SSA_gotot &) = 0;
  virtual void visit(const SSA_constraintt &) = 0;
  virtual void visit(const SSA_locationt &) = 0;
  virtual void visit(const SSA_outputt &) = 0;
  virtual void visit(const SSA_declt &) = 0;
  virtual void visit(const SSA_deadt &) = 0;
  virtual void visit(const SSA_function_callt &) = 0;
  virtual void visit(const SSA_function_returnt &) = 0;
  virtual void visit(const SSA_shared_readt &) = 0;
  virtual void visit(const SSA_shared_writet &) = 0;
  virtual void visit(const SSA_spawnt &) = 0;
  virtual void visit(const SSA_memory_barriert &) = 0;
  virtual void visit(const SSA_atomic_begint &) = 0;
  virtual void visit(const SSA_atomic_endt &) = 0;
  virtual void visit(const SSA_inputt &) = 0;
};

class SSA_const_visitor_const_argst
{
public:
  virtual ~SSA_const_visitor_const_argst() = default;

  virtual void visit(const SSA_assertt &) const = 0;
  virtual void visit(const SSA_assumet &) const = 0;
  virtual void visit(const SSA_assignmentt &) const = 0;
  virtual void visit(const SSA_gotot &) const = 0;
  virtual void visit(const SSA_constraintt &) const = 0;
  virtual void visit(const SSA_locationt &) const = 0;
  virtual void visit(const SSA_outputt &) const = 0;
  virtual void visit(const SSA_declt &) const = 0;
  virtual void visit(const SSA_deadt &) const = 0;
  virtual void visit(const SSA_function_callt &) const = 0;
  virtual void visit(const SSA_function_returnt &) const = 0;
  virtual void visit(const SSA_shared_readt &) const = 0;
  virtual void visit(const SSA_shared_writet &) const = 0;
  virtual void visit(const SSA_spawnt &) const = 0;
  virtual void visit(const SSA_memory_barriert &) const = 0;
  virtual void visit(const SSA_atomic_begint &) const = 0;
  virtual void visit(const SSA_atomic_endt &) const = 0;
  virtual void visit(const SSA_inputt &) const = 0;
};

class SSA_visitort
{
public:
  virtual ~SSA_visitort() = default;

  virtual void visit(SSA_assertt &) = 0;
  virtual void visit(SSA_assumet &) = 0;
  virtual void visit(SSA_assignmentt &) = 0;
  virtual void visit(SSA_gotot &) = 0;
  virtual void visit(SSA_constraintt &) = 0;
  virtual void visit(SSA_locationt &) = 0;
  virtual void visit(SSA_outputt &) = 0;
  virtual void visit(SSA_declt &) = 0;
  virtual void visit(SSA_deadt &) = 0;
  virtual void visit(SSA_function_callt &) = 0;
  virtual void visit(SSA_function_returnt &) = 0;
  virtual void visit(SSA_shared_readt &) = 0;
  virtual void visit(SSA_shared_writet &) = 0;
  virtual void visit(SSA_spawnt &) = 0;
  virtual void visit(SSA_memory_barriert &) = 0;
  virtual void visit(SSA_atomic_begint &) = 0;
  virtual void visit(SSA_atomic_endt &) = 0;
  virtual void visit(SSA_inputt &) = 0;
};

class SSA_const_visitort
{
public:
  virtual ~SSA_const_visitort() = default;

  virtual void visit(SSA_assertt &) const = 0;
  virtual void visit(SSA_assumet &) const = 0;
  virtual void visit(SSA_assignmentt &) const = 0;
  virtual void visit(SSA_gotot &) const = 0;
  virtual void visit(SSA_constraintt &) const = 0;
  virtual void visit(SSA_locationt &) const = 0;
  virtual void visit(SSA_outputt &) const = 0;
  virtual void visit(SSA_declt &) const = 0;
  virtual void visit(SSA_deadt &) const = 0;
  virtual void visit(SSA_function_callt &) const = 0;
  virtual void visit(SSA_function_returnt &) const = 0;
  virtual void visit(SSA_shared_readt &) const = 0;
  virtual void visit(SSA_shared_writet &) const = 0;
  virtual void visit(SSA_spawnt &) const = 0;
  virtual void visit(SSA_memory_barriert &) const = 0;
  virtual void visit(SSA_atomic_begint &) const = 0;
  virtual void visit(SSA_atomic_endt &) const = 0;
  virtual void visit(SSA_inputt &) const = 0;
};

class SSA_stept
{
public:
  virtual ~SSA_stept()=default;
  symex_targett::sourcet source;

  virtual bool is_assert() const          { return false; }
  virtual bool is_assume() const          { return false; }
  virtual bool is_assignment() const      { return false; }
  virtual bool is_goto() const            { return false; }
  virtual bool is_constraint() const      { return false; }
  virtual bool is_location() const        { return false; }
  virtual bool is_output() const          { return false; }
  virtual bool is_decl() const            { return false; }
  virtual bool is_function_call() const   { return false; }
  virtual bool is_function_return() const { return false; }
  virtual bool is_shared_read() const     { return false; }
  virtual bool is_shared_write() const    { return false; }
  virtual bool is_spawn() const           { return false; }
  virtual bool is_memory_barrier() const  { return false; }
  virtual bool is_atomic_begin() const    { return false; }
  virtual bool is_atomic_end() const      { return false; }

  // we may choose to hide
  bool hidden=false;

  exprt guard;
  literalt guard_literal;

  // for ASSIGNMENT and DECL
  ssa_exprt ssa_lhs;
  exprt ssa_full_lhs, original_full_lhs;
  exprt ssa_rhs;
  typedef symex_targett::assignment_typet assignment_typet;
  assignment_typet assignment_type;

  // for ASSUME/ASSERT/GOTO/CONSTRAINT
  exprt cond_expr;
  literalt cond_literal;
  std::string comment;

  // for INPUT/OUTPUT
  irep_idt format_string, io_id;
  bool formatted=false;
  std::list<exprt> io_args;
  std::list<exprt> converted_io_args;

  // for function call/return
  irep_idt identifier;

  // for SHARED_READ/SHARED_WRITE and ATOMIC_BEGIN/ATOMIC_END
  unsigned atomic_section_id=0;

  // for slicing
  bool ignore=false;

  void output(
    const namespacet &ns,
    std::ostream &out) const;

  virtual void accept(SSA_visitor_const_argst &) const = 0;
  virtual void accept(const SSA_const_visitor_const_argst &) const = 0;
  virtual void accept(SSA_visitort &) = 0;
  virtual void accept(const SSA_const_visitort &) = 0;

  virtual std::unique_ptr<goto_trace_stept> make_goto_trace_step() const = 0;

protected:
  SSA_stept():
    hidden(false),
    guard(static_cast<const exprt &>(get_nil_irep())),
    guard_literal(const_literal(false)),
    ssa_lhs(static_cast<const ssa_exprt &>(get_nil_irep())),
    ssa_full_lhs(static_cast<const exprt &>(get_nil_irep())),
    original_full_lhs(static_cast<const exprt &>(get_nil_irep())),
    ssa_rhs(static_cast<const exprt &>(get_nil_irep())),
    assignment_type(assignment_typet::STATE),
    cond_expr(static_cast<const exprt &>(get_nil_irep())),
    cond_literal(const_literal(false)),
    formatted(false),
    atomic_section_id(0),
    ignore(false)
  {
  }

private:
  virtual std::string custom_output(const namespacet &ns) const = 0;
};

template <typename T>
class SSA_acceptor_mixint : public SSA_stept
{
  void accept(SSA_visitor_const_argst &v) const override
  {
    v.visit(get_base());
  }
  void accept(const SSA_const_visitor_const_argst &v) const override
  {
    v.visit(get_base());
  }
  void accept(SSA_visitort &v) override
  {
    v.visit(get_base());
  }
  void accept(const SSA_const_visitort &v) override
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

class SSA_assertt : public SSA_acceptor_mixint<SSA_assertt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_assertt>();
  }

  bool is_assert() const          override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_assumet : public SSA_acceptor_mixint<SSA_assumet>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_assumet>();
  }

  bool is_assume() const          override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_assignmentt : public SSA_acceptor_mixint<SSA_assignmentt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_assignmentt>();
  }

  bool is_assignment() const      override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_gotot : public SSA_acceptor_mixint<SSA_gotot>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_gotot>();
  }

  bool is_goto() const            override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_constraintt : public SSA_acceptor_mixint<SSA_constraintt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_constraintt>();
  }

  bool is_constraint() const      override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_locationt : public SSA_acceptor_mixint<SSA_locationt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_locationt>();
  }

  bool is_location() const        override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_outputt : public SSA_acceptor_mixint<SSA_outputt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_outputt>();
  }

  bool is_output() const          override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_declt : public SSA_acceptor_mixint<SSA_declt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_declt>();
  }

  bool is_decl() const            override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_deadt : public SSA_acceptor_mixint<SSA_deadt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_deadt>();
  }

private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_function_callt : public SSA_acceptor_mixint<SSA_function_callt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_function_callt>();
  }

  bool is_function_call() const   override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_function_returnt : public SSA_acceptor_mixint<SSA_function_returnt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_function_returnt>();
  }

  bool is_function_return() const override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_shared_readt : public SSA_acceptor_mixint<SSA_shared_readt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_shared_readt>();
  }

  bool is_shared_read() const     override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_shared_writet : public SSA_acceptor_mixint<SSA_shared_writet>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_shared_writet>();
  }

  bool is_shared_write() const    override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_spawnt : public SSA_acceptor_mixint<SSA_spawnt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_spawnt>();
  }

  bool is_spawn() const           override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_memory_barriert : public SSA_acceptor_mixint<SSA_memory_barriert>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_memory_barriert>();
  }

  bool is_memory_barrier() const  override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_atomic_begint : public SSA_acceptor_mixint<SSA_atomic_begint>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_atomic_begint>();
  }

  bool is_atomic_begin() const    override { return true; }
private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_atomic_endt : public SSA_acceptor_mixint<SSA_atomic_endt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_atomic_endt>();
  }

  bool is_atomic_end() const      override { return true; }

private:
  std::string custom_output(const namespacet &ns) const override;
};

class SSA_inputt : public SSA_acceptor_mixint<SSA_inputt>
{
public:
  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_inputt>();
  }

private:
  std::string custom_output(const namespacet &ns) const override;
};

class defaulted_SSA_const_visitor_const_argst
  : public SSA_const_visitor_const_argst
{
public:
  virtual void default_visit(const SSA_stept &) const = 0;

  void visit(const SSA_assertt &x) const override { default_visit(x); }
  void visit(const SSA_assumet &x) const override { default_visit(x); }
  void visit(const SSA_assignmentt &x) const override { default_visit(x); }
  void visit(const SSA_gotot &x) const override { default_visit(x); }
  void visit(const SSA_constraintt &x) const override { default_visit(x); }
  void visit(const SSA_locationt &x) const override { default_visit(x); }
  void visit(const SSA_outputt &x) const override { default_visit(x); }
  void visit(const SSA_declt &x) const override { default_visit(x); }
  void visit(const SSA_deadt &x) const override { default_visit(x); }
  void visit(const SSA_function_callt &x) const override { default_visit(x); }
  void visit(const SSA_function_returnt &x) const override { default_visit(x); }
  void visit(const SSA_shared_readt &x) const override { default_visit(x); }
  void visit(const SSA_shared_writet &x) const override { default_visit(x); }
  void visit(const SSA_spawnt &x) const override { default_visit(x); }
  void visit(const SSA_memory_barriert &x) const override { default_visit(x); }
  void visit(const SSA_atomic_begint &x) const override { default_visit(x); }
  void visit(const SSA_atomic_endt &x) const override { default_visit(x); }
  void visit(const SSA_inputt &x) const override { default_visit(x); }
};

class defaulted_SSA_const_visitort : public SSA_const_visitort
{
public:
  virtual void default_visit(SSA_stept &) const = 0;

  void visit(SSA_assertt &x) const override { default_visit(x); }
  void visit(SSA_assumet &x) const override { default_visit(x); }
  void visit(SSA_assignmentt &x) const override { default_visit(x); }
  void visit(SSA_gotot &x) const override { default_visit(x); }
  void visit(SSA_constraintt &x) const override { default_visit(x); }
  void visit(SSA_locationt &x) const override { default_visit(x); }
  void visit(SSA_outputt &x) const override { default_visit(x); }
  void visit(SSA_declt &x) const override { default_visit(x); }
  void visit(SSA_deadt &x) const override { default_visit(x); }
  void visit(SSA_function_callt &x) const override { default_visit(x); }
  void visit(SSA_function_returnt &x) const override { default_visit(x); }
  void visit(SSA_shared_readt &x) const override { default_visit(x); }
  void visit(SSA_shared_writet &x) const override { default_visit(x); }
  void visit(SSA_spawnt &x) const override { default_visit(x); }
  void visit(SSA_memory_barriert &x) const override { default_visit(x); }
  void visit(SSA_atomic_begint &x) const override { default_visit(x); }
  void visit(SSA_atomic_endt &x) const override { default_visit(x); }
  void visit(SSA_inputt &x) const override { default_visit(x); }
};

class symex_target_equationt:public symex_targett
{
public:
  typedef ::SSA_stept SSA_stept;
  explicit symex_target_equationt(const namespacet &_ns);
  virtual ~symex_target_equationt();

  // read event
  virtual void shared_read(
    const exprt &guard,
    const ssa_exprt &ssa_object,
    unsigned atomic_section_id,
    const sourcet &source);

  // write event
  virtual void shared_write(
    const exprt &guard,
    const ssa_exprt &ssa_object,
    unsigned atomic_section_id,
    const sourcet &source);

  // assignment to a variable - lhs must be symbol
  virtual void assignment(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const exprt &ssa_full_lhs,
    const exprt &original_full_lhs,
    const exprt &ssa_rhs,
    const sourcet &source,
    assignment_typet assignment_type);

  // declare fresh variable - lhs must be symbol
  virtual void decl(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source,
    assignment_typet assignment_type);

  // note the death of a variable - lhs must be symbol
  virtual void dead(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source);

  // record a function call
  virtual void function_call(
    const exprt &guard,
    const irep_idt &identifier,
    const sourcet &source);

  // record return from a function
  virtual void function_return(
    const exprt &guard,
    const irep_idt &identifier,
    const sourcet &source);

  // just record a location
  virtual void location(
    const exprt &guard,
    const sourcet &source);

  // output
  virtual void output(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &fmt,
    const std::list<exprt> &args);

  // output, formatted
  virtual void output_fmt(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const irep_idt &fmt,
    const std::list<exprt> &args);

  // input
  virtual void input(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &input_id,
    const std::list<exprt> &args);

  // record an assumption
  virtual void assumption(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source);

  // record an assertion
  virtual void assertion(
    const exprt &guard,
    const exprt &cond,
    const std::string &msg,
    const sourcet &source);

  // record a goto
  virtual void goto_instruction(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source);

  // record a (global) constraint
  virtual void constraint(
    const exprt &cond,
    const std::string &msg,
    const sourcet &source);

  // record thread spawn
  virtual void spawn(
    const exprt &guard,
    const sourcet &source);

  // record memory barrier
  virtual void memory_barrier(
    const exprt &guard,
    const sourcet &source);

  // record atomic section
  virtual void atomic_begin(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source);
  virtual void atomic_end(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source);

  void convert(prop_convt &prop_conv);
  void convert_assignments(decision_proceduret &decision_procedure) const;
  void convert_decls(prop_convt &prop_conv) const;
  void convert_assumptions(prop_convt &prop_conv);
  void convert_assertions(prop_convt &prop_conv);
  void convert_constraints(decision_proceduret &decision_procedure) const;
  void convert_goto_instructions(prop_convt &prop_conv);
  void convert_guards(prop_convt &prop_conv);
  void convert_io(decision_proceduret &decision_procedure);

  exprt make_expression() const;


  std::size_t count_assertions() const
  {
    std::size_t i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if((*it)->is_assert())
        i++;
    return i;
  }

  std::size_t count_ignored_SSA_steps() const
  {
    std::size_t i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if((*it)->ignore)
        i++;
    return i;
  }

  typedef std::list<std::unique_ptr<SSA_stept>> SSA_stepst;
  SSA_stepst SSA_steps;

  SSA_stepst::iterator get_SSA_step(std::size_t s)
  {
    SSA_stepst::iterator it=SSA_steps.begin();
    for(; s!=0; s--)
    {
      assert(it!=SSA_steps.end());
      it++;
    }
    return it;
  }

  void output(std::ostream &out) const;

  void clear()
  {
    SSA_steps.clear();
  }

  bool has_threads() const
  {
    for(SSA_stepst::const_iterator it=SSA_steps.begin();
        it!=SSA_steps.end();
        it++)
      if((*it)->source.thread_nr!=0)
        return true;

    return false;
  }

protected:
  const namespacet &ns;

  // for enforcing sharing in the expressions stored
  merge_irept merge_irep;
  void merge_ireps(SSA_stept &SSA_step);
};

inline bool operator<(
  const symex_target_equationt::SSA_stepst::const_iterator a,
  const symex_target_equationt::SSA_stepst::const_iterator b)
{
  return &(*a)<&(*b);
}

std::ostream &operator<<(
  std::ostream &out,
  const symex_target_equationt::SSA_stept &step);
std::ostream &operator<<(
  std::ostream &out,
  const symex_target_equationt &equation);

#endif // CPROVER_GOTO_SYMEX_SYMEX_TARGET_EQUATION_H

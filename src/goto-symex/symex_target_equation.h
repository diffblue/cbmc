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
#include <util/visitor_generator.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_trace.h>

#include <solvers/prop/literal.h>

#include "symex_target.h"

class decision_proceduret;
class namespacet;
class prop_convt;

class SSA_assertt;
class SSA_assumet;
class SSA_assignmentt;
class SSA_gotot;
class SSA_constraintt;
class SSA_locationt;
class SSA_outputt;
class SSA_declt;
class SSA_function_callt;
class SSA_function_returnt;
class SSA_shared_readt;
class SSA_shared_writet;
class SSA_spawnt;
class SSA_memory_barriert;
class SSA_atomic_begint;
class SSA_atomic_endt;
class SSA_inputt;

namespace detail
{
using SSA_step_ref_typest = typelistt<SSA_assertt &,
                                      SSA_assumet &,
                                      SSA_assignmentt &,
                                      SSA_gotot &,
                                      SSA_constraintt &,
                                      SSA_locationt &,
                                      SSA_outputt &,
                                      SSA_declt &,
                                      SSA_function_callt &,
                                      SSA_function_returnt &,
                                      SSA_shared_readt &,
                                      SSA_shared_writet &,
                                      SSA_spawnt &,
                                      SSA_memory_barriert &,
                                      SSA_atomic_begint &,
                                      SSA_atomic_endt &,
                                      SSA_inputt &>;

using SSA_step_const_ref_typest = typelistt<const SSA_assertt &,
                                            const SSA_assumet &,
                                            const SSA_assignmentt &,
                                            const SSA_gotot &,
                                            const SSA_constraintt &,
                                            const SSA_locationt &,
                                            const SSA_outputt &,
                                            const SSA_declt &,
                                            const SSA_function_callt &,
                                            const SSA_function_returnt &,
                                            const SSA_shared_readt &,
                                            const SSA_shared_writet &,
                                            const SSA_spawnt &,
                                            const SSA_memory_barriert &,
                                            const SSA_atomic_begint &,
                                            const SSA_atomic_endt &,
                                            const SSA_inputt &>;

} // namespace detail

using SSA_visitor_const_argst =
  visitor_generatort<detail::SSA_step_const_ref_typest>;
using SSA_const_visitor_const_argst =
  const_visitor_generatort<detail::SSA_step_const_ref_typest>;
using SSA_visitort = visitor_generatort<detail::SSA_step_ref_typest>;
using SSA_const_visitort =
  const_visitor_generatort<detail::SSA_step_ref_typest>;

class SSA_stept
{
public:
  virtual ~SSA_stept()=default;
  symex_targett::sourcet source;

  virtual goto_trace_stept::typet type() const = 0;

  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_assert() const          { return type()==goto_trace_stept::typet::ASSERT; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_assume() const          { return type()==goto_trace_stept::typet::ASSUME; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_assignment() const      { return type()==goto_trace_stept::typet::ASSIGNMENT; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_goto() const            { return type()==goto_trace_stept::typet::GOTO; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_constraint() const      { return type()==goto_trace_stept::typet::CONSTRAINT; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_location() const        { return type()==goto_trace_stept::typet::LOCATION; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_output() const          { return type()==goto_trace_stept::typet::OUTPUT; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_decl() const            { return type()==goto_trace_stept::typet::DECL; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_function_call() const   { return type()==goto_trace_stept::typet::FUNCTION_CALL; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_function_return() const { return type()==goto_trace_stept::typet::FUNCTION_RETURN; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_shared_read() const     { return type()==goto_trace_stept::typet::SHARED_READ; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_shared_write() const    { return type()==goto_trace_stept::typet::SHARED_WRITE; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_spawn() const           { return type()==goto_trace_stept::typet::SPAWN; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_memory_barrier() const  { return type()==goto_trace_stept::typet::MEMORY_BARRIER; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_atomic_begin() const    { return type()==goto_trace_stept::typet::ATOMIC_BEGIN; }
  // NOLINTNEXTLINE(whitespace/line_length)
  bool is_atomic_end() const      { return type()==goto_trace_stept::typet::ATOMIC_END; }

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
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::ASSERT; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_assertt>();
  }
};

class SSA_assumet : public SSA_acceptor_mixint<SSA_assumet>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::ASSUME; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_assumet>();
  }
};

class SSA_assignmentt : public SSA_acceptor_mixint<SSA_assignmentt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::ASSIGNMENT; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_assignmentt>();
  }
};

class SSA_gotot : public SSA_acceptor_mixint<SSA_gotot>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::GOTO; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_gotot>();
  }
};

class SSA_constraintt : public SSA_acceptor_mixint<SSA_constraintt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::CONSTRAINT; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_constraintt>();
  }
};

class SSA_locationt : public SSA_acceptor_mixint<SSA_locationt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::LOCATION; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_locationt>();
  }
};

class SSA_outputt : public SSA_acceptor_mixint<SSA_outputt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::OUTPUT; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_outputt>();
  }
};

class SSA_declt : public SSA_acceptor_mixint<SSA_declt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::DECL; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_declt>();
  }
};

class SSA_function_callt : public SSA_acceptor_mixint<SSA_function_callt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::FUNCTION_CALL; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_function_callt>();
  }
};

class SSA_function_returnt : public SSA_acceptor_mixint<SSA_function_returnt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::FUNCTION_RETURN; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_function_returnt>();
  }
};

class SSA_shared_readt : public SSA_acceptor_mixint<SSA_shared_readt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::SHARED_READ; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_shared_readt>();
  }
};

class SSA_shared_writet : public SSA_acceptor_mixint<SSA_shared_writet>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::SHARED_WRITE; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_shared_writet>();
  }
};

class SSA_spawnt : public SSA_acceptor_mixint<SSA_spawnt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::SPAWN; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_spawnt>();
  }
};

class SSA_memory_barriert : public SSA_acceptor_mixint<SSA_memory_barriert>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::MEMORY_BARRIER; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_memory_barriert>();
  }
};

class SSA_atomic_begint : public SSA_acceptor_mixint<SSA_atomic_begint>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::ATOMIC_BEGIN; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_atomic_begint>();
  }
};

class SSA_atomic_endt : public SSA_acceptor_mixint<SSA_atomic_endt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::ATOMIC_END; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_atomic_endt>();
  }
};

class SSA_inputt : public SSA_acceptor_mixint<SSA_inputt>
{
public:
  goto_trace_stept::typet type() const override
  { return goto_trace_stept::typet::INPUT; }

  std::unique_ptr<goto_trace_stept> make_goto_trace_step() const override
  {
    return util_make_unique<trace_inputt>();
  }
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

/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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

class symex_target_equationt:public symex_targett
{
public:
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

  class SSA_stept
  {
  public:
    sourcet source;
    goto_trace_stept::typet type;

    bool is_assert() const          { return type==goto_trace_stept::ASSERT; }
    bool is_assume() const          { return type==goto_trace_stept::ASSUME; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_assignment() const      { return type==goto_trace_stept::ASSIGNMENT; }
    bool is_goto() const            { return type==goto_trace_stept::GOTO; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_constraint() const      { return type==goto_trace_stept::CONSTRAINT; }
    bool is_location() const        { return type==goto_trace_stept::LOCATION; }
    bool is_output() const          { return type==goto_trace_stept::OUTPUT; }
    bool is_decl() const            { return type==goto_trace_stept::DECL; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_function_call() const   { return type==goto_trace_stept::FUNCTION_CALL; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_function_return() const { return type==goto_trace_stept::FUNCTION_RETURN; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_shared_read() const     { return type==goto_trace_stept::SHARED_READ; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_shared_write() const    { return type==goto_trace_stept::SHARED_WRITE; }
    bool is_spawn() const           { return type==goto_trace_stept::SPAWN; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_memory_barrier() const  { return type==goto_trace_stept::MEMORY_BARRIER; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_atomic_begin() const    { return type==goto_trace_stept::ATOMIC_BEGIN; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_atomic_end() const      { return type==goto_trace_stept::ATOMIC_END; }

    // we may choose to hide
    bool hidden=false;

    exprt guard;
    literalt guard_literal;

    // for ASSIGNMENT and DECL
    ssa_exprt ssa_lhs;
    exprt ssa_full_lhs, original_full_lhs;
    exprt ssa_rhs;
    assignment_typet assignment_type=assignment_typet::STATE;

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

    SSA_stept():
      type(goto_trace_stept::NONE),
      hidden(false),
      guard(static_cast<const exprt &>(get_nil_irep())),
      guard_literal(const_literal(false)),
      ssa_lhs(static_cast<const ssa_exprt &>(get_nil_irep())),
      ssa_full_lhs(static_cast<const exprt &>(get_nil_irep())),
      original_full_lhs(static_cast<const exprt &>(get_nil_irep())),
      ssa_rhs(static_cast<const exprt &>(get_nil_irep())),
      cond_expr(static_cast<const exprt &>(get_nil_irep())),
      cond_literal(const_literal(false)),
      formatted(false),
      atomic_section_id(0),
      ignore(false)
    {
    }

    void output(
      const namespacet &ns,
      std::ostream &out) const;
  };

  unsigned count_assertions() const
  {
    unsigned i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if(it->is_assert())
        i++;
    return i;
  }

  unsigned count_ignored_SSA_steps() const
  {
    unsigned i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if(it->ignore)
        i++;
    return i;
  }

  typedef std::list<SSA_stept> SSA_stepst;
  SSA_stepst SSA_steps;

  SSA_stepst::iterator get_SSA_step(unsigned s)
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
      if(it->source.thread_nr!=0)
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

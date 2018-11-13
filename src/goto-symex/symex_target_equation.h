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

#include <util/invariant.h>
#include <util/merge_irep.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_trace.h>

#include <solvers/prop/literal.h>

#include "symex_target.h"

class decision_proceduret;
class namespacet;
class prop_convt;

/// Inheriting the interface of symex_targett this class represents the SSA
/// form of the input program as a list of \ref SSA_stept. It further extends
/// the base class by providing a conversion interface for decision procedures.
class symex_target_equationt:public symex_targett
{
public:
  virtual ~symex_target_equationt() = default;

  /// \copydoc symex_targett::shared_read()
  virtual void shared_read(
    const exprt &guard,
    const ssa_exprt &ssa_object,
    unsigned atomic_section_id,
    const sourcet &source);

  /// \copydoc symex_targett::shared_write()
  virtual void shared_write(
    const exprt &guard,
    const ssa_exprt &ssa_object,
    unsigned atomic_section_id,
    const sourcet &source);

  /// \copydoc symex_targett::assignment()
  virtual void assignment(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const exprt &ssa_full_lhs,
    const exprt &original_full_lhs,
    const exprt &ssa_rhs,
    const sourcet &source,
    assignment_typet assignment_type);

  /// \copydoc symex_targett::decl()
  virtual void decl(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source,
    assignment_typet assignment_type);

  /// \copydoc symex_targett::dead()
  virtual void dead(
    const exprt &guard,
    const ssa_exprt &ssa_lhs,
    const sourcet &source);

  /// \copydoc symex_targett::function_call()
  virtual void function_call(
    const exprt &guard,
    const irep_idt &function_identifier,
    const std::vector<exprt> &ssa_function_arguments,
    const sourcet &source,
    bool hidden);

  /// \copydoc symex_targett::function_return()
  virtual void
  function_return(const exprt &guard, const sourcet &source, bool hidden);

  /// \copydoc symex_targett::location()
  virtual void location(
    const exprt &guard,
    const sourcet &source);

  /// \copydoc symex_targett::output()
  virtual void output(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const std::list<exprt> &args);

  /// \copydoc symex_targett::output_fmt()
  virtual void output_fmt(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const irep_idt &fmt,
    const std::list<exprt> &args);

  /// \copydoc symex_targett::input()
  virtual void input(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &input_id,
    const std::list<exprt> &args);

  /// \copydoc symex_targett::assumption()
  virtual void assumption(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source);

  /// \copydoc symex_targett::assertion()
  virtual void assertion(
    const exprt &guard,
    const exprt &cond,
    const std::string &msg,
    const sourcet &source);

  /// \copydoc symex_targett::goto_instruction()
  virtual void goto_instruction(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source);

  /// \copydoc symex_targett::constraint()
  virtual void constraint(
    const exprt &cond,
    const std::string &msg,
    const sourcet &source);

  /// \copydoc symex_targett::spawn()
  virtual void spawn(
    const exprt &guard,
    const sourcet &source);

  /// \copydoc symex_targett::memory_barrier()
  virtual void memory_barrier(
    const exprt &guard,
    const sourcet &source);

  /// \copydoc symex_targett::atomic_begin()
  virtual void atomic_begin(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source);

  /// \copydoc symex_targett::atomic_end()
  virtual void atomic_end(
    const exprt &guard,
    unsigned atomic_section_id,
    const sourcet &source);

  /// Interface method to initiate the conversion into a decision procedure
  /// format. The method iterates over the equation, i.e. over the SSA steps and
  /// converts each type of step separately.
  /// \param prop_conv: A handle to a particular decision procedure interface
  void convert(prop_convt &prop_conv);

  /// Converts assignments: set the equality _lhs==rhs_ to _True_.
  /// \param decision_procedure: A handle to a particular decision procedure
  ///  interface
  void convert_assignments(decision_proceduret &decision_procedure) const;

  /// Converts declarations: these are effectively ignored by the decision
  /// procedure.
  /// \param prop_conv: A handle to a particular decision procedure interface
  void convert_decls(prop_convt &prop_conv) const;

  /// Converts assumptions: convert the expression the assumption represents.
  /// \param prop_conv: A handle to a particular decision procedure interface
  void convert_assumptions(prop_convt &prop_conv);

  /// Converts assertions: build a disjunction of negated assertions.
  /// \param prop_conv: A handle to a particular decision procedure interface
  void convert_assertions(prop_convt &prop_conv);

  /// Converts constraints: set the represented condition to _True_.
  /// \param decision_procedure: A handle to a particular decision procedure
  ///  interface
  void convert_constraints(decision_proceduret &decision_procedure) const;

  /// Converts goto instructions: convert the expression representing the
  /// condition of this goto.
  /// \param prop_conv: A handle to a particular decision procedure interface
  void convert_goto_instructions(prop_convt &prop_conv);

  /// Converts guards: convert the expression the guard represents.
  /// \param prop_conv: A handle to a particular decision procedure interface
  void convert_guards(prop_convt &prop_conv);

  /// Converts function calls: for each argument build an equality between its
  /// symbol and the argument itself.
  /// \param decision_procedure: A handle to a particular decision procedure
  ///  interface
  void convert_function_calls(decision_proceduret &decision_procedure);

  /// Converts I/O: for each argument build an equality between its
  /// symbol and the argument itself.
  /// \param decision_procedure: A handle to a particular decision procedure
  ///  interface
  void convert_io(decision_proceduret &decision_procedure);

  exprt make_expression() const;

  /// Single SSA step in the equation. Its `type` is defined as
  /// goto_trace_stept::typet. Every SSA step has a `source` to identify its
  /// origin in the input GOTO program and a `guard` expression which holds
  /// the path condition required to reach this step: they limit the scope of
  /// this step.
  ///
  /// SSA steps that represent assignments and declarations also store the
  /// left- and right-hand sides of the assignment. The left-hand side
  /// `ssa_lhs` is required to be of type ssa_exprt: in SSA form, variables
  /// are only assigned once, see \ref static-single-assignment. To achieve
  /// that, we annotate the original name with 3 types of levels, see
  /// ssa_exprt. The assignment step also represents the left-hand side in two
  /// other _full_ forms: `ssa_full_lhs` and `original_full_lhs`, which store
  /// the original expressions from the input GOTO program before removing
  /// array indexes, pointers, etc. The `ssa_full_lhs` uses the level-annotated
  /// names.
  ///
  /// Assumptions, assertions, goto steps, and constraints have `cond_expr`
  /// which represent the condition guarding this step, i.e. what must hold for
  /// this step to be taken. Both `guard` and `cond_expr` will later be
  /// translated into verification condition for the SAT/SMT solver (or some
  /// other decision procedure), to be referred by their respective literals.
  /// Constraints usually arise from external conditions, such as memory models
  /// or partial orders: they represent assumptions with global effect.
  ///
  /// Function calls store `called_function` name as well as a vector of
  /// arguments `ssa_function_arguments`. The `converted` version of a
  /// variable will contain its version for the SAT/SMT conversion.
  class SSA_stept
  {
  public:
    sourcet source;
    goto_trace_stept::typet type;

    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_assert() const          { return type==goto_trace_stept::typet::ASSERT; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_assume() const          { return type==goto_trace_stept::typet::ASSUME; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_assignment() const      { return type==goto_trace_stept::typet::ASSIGNMENT; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_goto() const            { return type==goto_trace_stept::typet::GOTO; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_constraint() const      { return type==goto_trace_stept::typet::CONSTRAINT; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_location() const        { return type==goto_trace_stept::typet::LOCATION; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_output() const          { return type==goto_trace_stept::typet::OUTPUT; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_decl() const            { return type==goto_trace_stept::typet::DECL; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_function_call() const   { return type==goto_trace_stept::typet::FUNCTION_CALL; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_function_return() const { return type==goto_trace_stept::typet::FUNCTION_RETURN; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_shared_read() const     { return type==goto_trace_stept::typet::SHARED_READ; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_shared_write() const    { return type==goto_trace_stept::typet::SHARED_WRITE; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_spawn() const           { return type==goto_trace_stept::typet::SPAWN; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_memory_barrier() const  { return type==goto_trace_stept::typet::MEMORY_BARRIER; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_atomic_begin() const    { return type==goto_trace_stept::typet::ATOMIC_BEGIN; }
    // NOLINTNEXTLINE(whitespace/line_length)
    bool is_atomic_end() const      { return type==goto_trace_stept::typet::ATOMIC_END; }

    // we may choose to hide
    bool hidden=false;

    exprt guard;
    literalt guard_literal;

    // for ASSIGNMENT and DECL
    ssa_exprt ssa_lhs;
    exprt ssa_full_lhs, original_full_lhs;
    exprt ssa_rhs;
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

    // for function calls: the function that is called
    irep_idt called_function;

    // for function calls
    std::vector<exprt> ssa_function_arguments,
                       converted_function_arguments;

    // for SHARED_READ/SHARED_WRITE and ATOMIC_BEGIN/ATOMIC_END
    unsigned atomic_section_id=0;

    // for slicing
    bool ignore=false;

    SSA_stept():
      type(goto_trace_stept::typet::NONE),
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

    DEPRECATED("Use output without ns param")
    void output(
      const namespacet &ns,
      std::ostream &out) const;

    void output(std::ostream &out) const;

    void validate(const namespacet &ns, const validation_modet vm) const;
  };

  std::size_t count_assertions() const
  {
    std::size_t i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if(it->is_assert())
        i++;
    return i;
  }

  std::size_t count_ignored_SSA_steps() const
  {
    std::size_t i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if(it->ignore)
        i++;
    return i;
  }

  typedef std::list<SSA_stept> SSA_stepst;
  SSA_stepst SSA_steps;

  SSA_stepst::iterator get_SSA_step(std::size_t s)
  {
    SSA_stepst::iterator it=SSA_steps.begin();
    for(; s!=0; s--)
    {
      PRECONDITION(it != SSA_steps.end());
      it++;
    }
    return it;
  }

  void output(std::ostream &out, const namespacet &ns) const;

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

  void validate(const namespacet &ns, const validation_modet vm) const
  {
    for(const SSA_stept &step : SSA_steps)
      step.validate(ns, vm);
  }

protected:
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

#endif // CPROVER_GOTO_SYMEX_SYMEX_TARGET_EQUATION_H

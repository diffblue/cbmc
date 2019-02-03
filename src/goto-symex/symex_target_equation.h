/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Generate Equation using Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_SYMEX_TARGET_EQUATION_H
#define CPROVER_GOTO_SYMEX_SYMEX_TARGET_EQUATION_H

#include <algorithm>
#include <iosfwd>
#include <list>

#include <util/invariant.h>
#include <util/merge_irep.h>
#include <util/message.h>
#include <util/narrow.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_trace.h>

#include "renaming_level.h"
#include "ssa_step.h"
#include "symex_target.h"

class decision_proceduret;
class namespacet;
class decision_proceduret;

/// Inheriting the interface of symex_targett this class represents the SSA
/// form of the input program as a list of \ref SSA_stept. It further extends
/// the base class by providing a conversion interface for decision procedures.
class symex_target_equationt:public symex_targett
{
public:
  explicit symex_target_equationt(message_handlert &message_handler)
    : log(message_handler)
  {
  }

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
    const irep_idt &function_id,
    const std::vector<renamedt<exprt, L2>> &ssa_function_arguments,
    const sourcet &source,
    bool hidden);

  /// \copydoc symex_targett::function_return()
  virtual void function_return(
    const exprt &guard,
    const irep_idt &function_id,
    const sourcet &source,
    bool hidden);

  /// \copydoc symex_targett::location()
  virtual void location(
    const exprt &guard,
    const sourcet &source);

  /// \copydoc symex_targett::output()
  virtual void output(
    const exprt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const std::list<renamedt<exprt, L2>> &args);

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
    const renamedt<exprt, L2> &cond,
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
  /// \param decision_procedure: A handle to a decision procedure interface
  void convert(decision_proceduret &decision_procedure);

  /// Interface method to initiate the conversion into a decision procedure
  /// format. The method iterates over the equation, i.e. over the SSA steps and
  /// converts each type of step separately, except assertions.
  /// This enables the caller to handle assertion conversion differently,
  /// e.g. for incremental solving.
  /// \param decision_procedure: A handle to a particular decision procedure
  ///   interface
  void convert_without_assertions(decision_proceduret &decision_procedure);

  /// Converts assignments: set the equality _lhs==rhs_ to _True_.
  /// \param decision_procedure: A handle to a decision procedure
  ///  interface
  void convert_assignments(decision_proceduret &decision_procedure);

  /// Converts declarations: these are effectively ignored by the decision
  /// procedure.
  /// \param decision_procedure: A handle to a decision procedure
  ///  interface
  void convert_decls(decision_proceduret &decision_procedure);

  /// Converts assumptions: convert the expression the assumption represents.
  /// \param decision_procedure: A handle to a decision procedure interface
  void convert_assumptions(decision_proceduret &decision_procedure);

  /// Converts assertions: build a disjunction of negated assertions.
  /// \param decision_procedure: A handle to a decision procedure interface
  /// \param optimized_for_single_assertions: Use an optimized encoding for
  ///   single assertions (unsound for incremental conversions)
  void convert_assertions(
    decision_proceduret &decision_procedure,
    bool optimized_for_single_assertions = true);

  /// Converts constraints: set the represented condition to _True_.
  /// \param decision_procedure: A handle to a decision procedure interface
  void convert_constraints(decision_proceduret &decision_procedure);

  /// Converts goto instructions: convert the expression representing the
  /// condition of this goto.
  /// \param decision_procedure: A handle to a decision procedure interface
  void convert_goto_instructions(decision_proceduret &decision_procedure);

  /// Converts guards: convert the expression the guard represents.
  /// \param decision_procedure: A handle to a decision procedure interface
  void convert_guards(decision_proceduret &decision_procedure);

  /// Converts function calls: for each argument build an equality between its
  /// symbol and the argument itself.
  /// \param decision_procedure: A handle to a decision procedure interface
  void convert_function_calls(decision_proceduret &decision_procedure);

  /// Converts I/O: for each argument build an equality between its
  /// symbol and the argument itself.
  /// \param decision_procedure: A handle to a decision procedure interface
  void convert_io(decision_proceduret &decision_procedure);

  exprt make_expression() const;

  std::size_t count_assertions() const
  {
    return narrow_cast<std::size_t>(std::count_if(
      SSA_steps.begin(), SSA_steps.end(), [](const SSA_stept &step) {
        return step.is_assert() && !step.ignore && !step.converted;
      }));
  }

  std::size_t count_ignored_SSA_steps() const
  {
    return narrow_cast<std::size_t>(std::count_if(
      SSA_steps.begin(), SSA_steps.end(), [](const SSA_stept &step) {
        return step.ignore;
      }));
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

  void output(std::ostream &out) const;

  void clear()
  {
    SSA_steps.clear();
  }

  bool has_threads() const
  {
    return std::any_of(
      SSA_steps.begin(), SSA_steps.end(), [](const SSA_stept &step) {
        return step.source.thread_nr != 0;
      });
  }

  void validate(const namespacet &ns, const validation_modet vm) const
  {
    for(const SSA_stept &step : SSA_steps)
      step.validate(ns, vm);
  }

protected:
  messaget log;

  // for enforcing sharing in the expressions stored
  merge_irept merge_irep;
  void merge_ireps(SSA_stept &SSA_step);

  // for unique I/O identifiers
  std::size_t io_count = 0;

  // for unique function call argument identifiers
  std::size_t argument_count = 0;
};

inline bool operator<(
  const symex_target_equationt::SSA_stepst::const_iterator a,
  const symex_target_equationt::SSA_stepst::const_iterator b)
{
  return &(*a)<&(*b);
}

#endif // CPROVER_GOTO_SYMEX_SYMEX_TARGET_EQUATION_H

/*******************************************************************\

Module: Decision Procedure Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Decision Procedure Interface

#ifndef CPROVER_SOLVERS_DECISION_PROCEDURE_H
#define CPROVER_SOLVERS_DECISION_PROCEDURE_H

#include <iosfwd>
#include <string>

class exprt;

/// An interface for a decision procedure for satisfiability problems.
///
/// A decision procedure follows a state machine:
///
///   D_ERROR ──operator()──► D_SATISFIABLE ──set_to()──► D_ERROR
///     ▲                        │
///     │                        └──get() valid
///     │
///   D_ERROR ──operator()──► D_UNSATISFIABLE ──set_to()──► D_ERROR
///
/// After construction, the procedure's status (\ref latest_result) is
/// initialised to D_ERROR, representing "not yet solved". Calling
/// \ref operator()() transitions to D_SATISFIABLE, D_UNSATISFIABLE, or D_ERROR.
/// Reading the satisfying assignment via \ref get is only valid in the
/// D_SATISFIABLE state. Adding new constraints (\ref set_to, \ref handle)
/// resets the status to D_ERROR.
class decision_proceduret
{
public:
  /// For a Boolean expression \p expr, add the constraint 'expr' if \p value
  /// is `true`, otherwise add 'not expr'
  virtual void set_to(const exprt &, bool value) = 0;

  /// For a Boolean expression \p expr, add the constraint 'expr'
  void set_to_true(const exprt &);

  /// For a Boolean expression \p expr, add the constraint 'not expr'
  void set_to_false(const exprt &);

  /// Generate a handle, which is an expression that
  /// has the same value as the argument in any model
  /// that is generated; this offers an efficient way
  /// to refer to the expression in subsequent calls to \ref get or
  /// \ref set_to.
  /// The returned expression may be the expression itself or a more compact
  /// but solver-specific representation.
  virtual exprt handle(const exprt &) = 0;

  /// Result of running the decision procedure
  enum class resultt
  {
    D_SATISFIABLE,
    D_UNSATISFIABLE,
    D_ERROR
  };

  /// Run the decision procedure to solve the problem
  /// This corresponds to SMT-LIB's check-sat.
  resultt operator()();

  /// Run the decision procedure to solve the problem under
  /// the given assumption.
  /// This corresponds to SMT-LIB's check-sat-assuming.
  resultt operator()(const exprt &assumption);

  /// Return \p expr with variables replaced by values from satisfying
  /// assignment if available.
  /// Return `nil` if not available.
  /// \pre The last call to \ref operator()() returned D_SATISFIABLE.
  virtual exprt get(const exprt &) const = 0;

  /// Print satisfying assignment to \p out
  virtual void print_assignment(std::ostream &out) const = 0;

  /// Return a textual description of the decision procedure
  virtual std::string decision_procedure_text() const = 0;

  /// Return the number of incremental solver calls
  virtual std::size_t get_number_of_solver_calls() const = 0;

  virtual ~decision_proceduret();

  /// Return the result of the last call to \ref operator()().
  /// \return The most recent result, or D_ERROR if not yet called.
  resultt get_status() const
  {
    return latest_result;
  }

protected:
  /// Implementation of the decision procedure.
  virtual resultt dec_solve(const exprt &assumption) = 0;

  resultt latest_result = resultt::D_ERROR;
};

/// Add Boolean constraint \p src to decision procedure \p dest
inline decision_proceduret &
operator<<(decision_proceduret &dest, const exprt &src)
{
  dest.set_to_true(src);
  return dest;
}

#endif // CPROVER_SOLVERS_DECISION_PROCEDURE_H

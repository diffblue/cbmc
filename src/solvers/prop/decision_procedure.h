/*******************************************************************\

Module: Decision Procedure Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Decision Procedure Interface

#ifndef CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_H
#define CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_H

#include <iosfwd>
#include <string>

#include "literal.h"

class exprt;
class tvt;

class decision_proceduret
{
public:
  /// For a Boolean expression \p expr, add the constraint 'expr' if \p value
  /// is `true`, otherwise add 'not expr'
  virtual void set_to(const exprt &expr, bool value) = 0;

  /// For a Boolean expression \p expr, add the constraint 'expr'
  void set_to_true(const exprt &expr);

  /// For a Boolean expression \p expr, add the constraint 'not expr'
  void set_to_false(const exprt &expr);

  /// Convert a Boolean expression and return the corresponding literal
  virtual literalt convert(const exprt &expr) = 0;

  /// Convert a Boolean expression and return the corresponding literal
  literalt operator()(const exprt &);

  /// Result of running the decision procedure
  enum class resultt
  {
    D_SATISFIABLE,
    D_UNSATISFIABLE,
    D_ERROR
  };

  /// Run the decision procedure to solve the problem
  resultt operator()();

  /// Return \p expr with variables replaced by values from satisfying
  /// assignment if available.
  /// Return `nil` if not available
  virtual exprt get(const exprt &expr) const = 0;

  /// Return value of literal \p l from satisfying assignment.
  /// Return tvt::UNKNOWN if not available
  virtual tvt l_get(literalt l) const = 0;

  /// Print satisfying assignment to \p out
  virtual void print_assignment(std::ostream &out) const = 0;

  /// Return a textual description of the decision procedure
  virtual std::string decision_procedure_text() const = 0;

  /// Return the number of incremental solver calls
  virtual std::size_t get_number_of_solver_calls() const = 0;

  virtual ~decision_proceduret();

protected:
  /// Run the decision procedure to solve the problem
  virtual resultt dec_solve() = 0;
};

/// Add Boolean constraint \p src to decision procedure \p dest
inline decision_proceduret &
operator<<(decision_proceduret &dest, const exprt &src)
{
  dest.set_to_true(src);
  return dest;
}

#endif // CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_H

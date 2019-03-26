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

class exprt;

class decision_proceduret
{
public:
  virtual ~decision_proceduret();

  // get a value from satisfying instance if satisfiable
  // returns nil if not available
  virtual exprt get(const exprt &expr) const=0;

  // print satisfying assignment
  virtual void print_assignment(std::ostream &out) const=0;

  // add constraints
  // the expression must be of Boolean type
  virtual void set_to(const exprt &expr, bool value)=0;

  void set_to_true(const exprt &expr)
  { set_to(expr, true); }

  void set_to_false(const exprt &expr)
  { set_to(expr, false); }

  // solve the problem
  enum class resultt { D_SATISFIABLE, D_UNSATISFIABLE, D_ERROR };

  // will eventually be protected, use below call operator
  virtual resultt dec_solve()=0;

  resultt operator()()
  {
    return dec_solve();
  }

  // return a textual description of the decision procedure
  virtual std::string decision_procedure_text() const=0;

  /// Returns the number of incremental solver calls
  virtual std::size_t get_number_of_solver_calls() const = 0;
};

inline decision_proceduret &operator<<(
  decision_proceduret &dest,
  const exprt &src)
{
  dest.set_to_true(src);
  return dest;
}

#endif // CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_H

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_PROP_CONV_H
#define CPROVER_SOLVERS_PROP_PROP_CONV_H

#include <solvers/decision_procedure.h>

#include "literal.h"

class tvt;

// API that provides a "handle" in the form of a literalt
// for expressions.

class prop_convt:public decision_proceduret
{
public:
  virtual ~prop_convt() { }

  using decision_proceduret::operator();

  /// returns a 'handle', which is an expression that
  /// has the same value as the argument in any model
  /// that is generated.
  /// This may be the expression itself or a more compact
  /// but solver-specific representation.
  exprt handle(const exprt &expr) override;

  /// Convert a Boolean expression and return the corresponding literal
  virtual literalt convert(const exprt &expr) = 0;

  /// Return value of literal \p l from satisfying assignment.
  /// Return tvt::UNKNOWN if not available
  virtual tvt l_get(literalt l) const = 0;

  // incremental solving
  virtual void set_frozen(literalt a);
  virtual void set_frozen(const bvt &);
  virtual void set_assumptions(const bvt &_assumptions);
  virtual bool has_set_assumptions() const { return false; }
  virtual void set_all_frozen() {}

  // returns true if an assumption is in the final conflict
  virtual bool is_in_conflict(literalt l) const;
  virtual bool has_is_in_conflict() const { return false; }
};

#endif // CPROVER_SOLVERS_PROP_PROP_CONV_H

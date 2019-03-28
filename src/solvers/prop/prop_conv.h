/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_PROP_CONV_H
#define CPROVER_SOLVERS_PROP_PROP_CONV_H

#include <solvers/stack_decision_procedure.h>

class literalt;
class tvt;

// API that provides a "handle" in the form of a literalt
// for expressions.

class prop_convt : public stack_decision_proceduret
{
public:
  virtual ~prop_convt() { }

  /// Convert a Boolean expression and return the corresponding literal
  virtual literalt convert(const exprt &expr) = 0;

  /// Return value of literal \p l from satisfying assignment.
  /// Return tvt::UNKNOWN if not available
  virtual tvt l_get(literalt l) const = 0;
};

#endif // CPROVER_SOLVERS_PROP_PROP_CONV_H

/*******************************************************************\

Module: Generate equation and solve upon encountering an assertion

Author: Michael Tautschnig

\*******************************************************************/

#if 0

/// \file
/// Generate equation and solve upon encountering an assertion

#  ifndef CPROVER_GOTO_SYMEX_EAGER_EQUATION_H
#    define CPROVER_GOTO_SYMEX_EAGER_EQUATION_H

#    include "symex_target_equation.h"

class decision_proceduret;
class namespacet;

/// Extends \ref symex_target_equationt by immediately solving after each
/// encountered assertion.
class eager_equationt:public symex_target_equationt
{
public:
  eager_equationt(message_handlert &message_handler, decision_proceduret &decision_procedure)
    : symex_target_equationt(message_handler), decision_procedure(decision_procedure)
  {
  }

  virtual ~eager_equationt() = default;

  /// \copydoc symex_targett::assertion()
  void assertion(
    const exprt &guard,
    const exprt &cond,
    const std::string &msg,
    const sourcet &source) override;

protected:
  decision_proceduret &decision_procedure;
};

#  endif

#endif // CPROVER_GOTO_SYMEX_EAGER_EQUATION_H

/*******************************************************************\

Module: Decision procedure with incremental solving with contexts
        and assumptions

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Decision procedure with incremental solving with contexts
/// and assumptions
///
/// Normally, solvers allow you only to add new conjuncts to the
/// formula, but not to remove parts of the formula once added.
///
/// Solvers that offer pushing/popping of contexts or
/// 'solving under assumptions' offer some ways to emulate
/// removing parts of the formula.
///
/// Example 1: push/pop contexts:
/// \code{.cpp}
/// dp.set_to_true(a);     // added permanently
/// resultt result = dp(); // solves formula 'a'
/// stack_decision_procedure.set_to_true(b); // added permanently
/// resultt result = dp(); // solves 'a && b'
/// dp.push();
/// dp.set_to_true(c);     // added inside a context: we can remove it later
/// resultt result = dp(); // solves 'a && b && c'
/// dp.pop();              // 'removes' c
/// dp.push();
/// dp.set_to_true(d);     // added inside a context: we can remove it later
/// resultt result = dp(); // solves 'a && b && d'
/// \endcode
///
/// Example 2: solving under assumptions:
/// \code{.cpp}
/// dp.set_to_true(a);     // added permanently
/// resultt result = dp(); // solves formula 'a'
/// h1 = dp.handle(c);
/// h2 = dp.handle(d)
/// dp.push({h1, h2});
/// resultt result = dp(); // solves formula 'a && c && d'
/// dp.pop();              // clear assumptions h1, h2
/// h1 = dp.handle(not_exprt(c)); // get negated handle for 'c'
/// dp.push({h1, h2});
/// resultt result = dp(); // solves formula 'a && !c && d'
/// \endcode

#ifndef CPROVER_SOLVERS_STACK_DECISION_PROCEDURE_H
#define CPROVER_SOLVERS_STACK_DECISION_PROCEDURE_H

#include <vector>

#include "decision_procedure.h"

class stack_decision_proceduret : public decision_proceduret
{
public:
  /// Pushes a new context on the stack that consists of the given
  /// (possibly empty vector of) \p assumptions.
  /// This context becomes a child context nested in the current context.
  /// An assumption is usually obtained by calling
  /// `decision_proceduret::handle`. Thus it can be a Boolean expression or
  /// something more solver-specific such as `literal_exprt`.
  /// An empty vector of assumptions counts as an element on the stack
  /// (and therefore needs to be popped), but has no effect beyond that.
  virtual void push(const std::vector<exprt> &assumptions) = 0;

  /// Push a new context on the stack
  /// This context becomes a child context nested in the current context.
  virtual void push() = 0;

  /// Pop whatever is on top of the stack.
  /// Popping from the empty stack results in an invariant violation.
  virtual void pop() = 0;

  virtual ~stack_decision_proceduret() = default;
};

#endif // CPROVER_SOLVERS_STACK_DECISION_PROCEDURE_H

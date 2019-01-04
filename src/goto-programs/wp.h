/*******************************************************************\

Module: Weakest Preconditions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Weakest Preconditions

#ifndef CPROVER_GOTO_PROGRAMS_WP_H
#define CPROVER_GOTO_PROGRAMS_WP_H

class codet;
class exprt;
class namespacet;

/// Compute the weakest precondition of the given program
/// piece \a code with respect to the expression \a post.
/// \param code: Program
/// \param post: Postcondition
/// \param ns: Namespace
/// \return Weakest precondition
exprt wp(
  const codet &code,
  const exprt &post,
  const namespacet &ns);

/// Approximate the non-deterministic choice in a way cheaper than by (proper)
/// quantification
void approximate_nondet(exprt &dest);

#endif // CPROVER_GOTO_PROGRAMS_WP_H

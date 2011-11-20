/*******************************************************************\

Module: Weakest Preconditions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_WP_H
#define CPROVER_WP_H

class codet;
class exprt;
class namespacet;

/*! \defgroup gr_wp Weakest precondition */

/*! \brief Compute the weakest precondition of the given program
 * piece \a code with respect to the expression \a post.
 * \param code  Program
 * \param post  Postcondition
 * \param ns    Namespace
 * \return Weakest precondition
 *
 * \ingroup gr_wp
*/
exprt wp(
  const codet &code,
  const exprt &post,
  const namespacet &ns);

/*! \brief approximate the non-deterministic choice
           in a way cheaper than by (proper) quantification
 * \ingroup gr_wp
*/           
           
void approximate_nondet(exprt &dest);

#endif

#ifndef FINITE_CALCULUS_H
#define FINITE_CALCULUS_H

#include <util/std_expr.h>

/*
 * Convert a factorial power to an expression using conventional powers.
 */
exprt factorial_pow_to_pow(exprt &e);

/*
 * Find the indefinite sum of e with respect to x.
 *
 * Written as \sum e \delta x
 *
 * The indefinite sum is the finite analogue of the indefinite integral.
 */
exprt indefinite_sum(const exprt &e, const exprt &x);


/*
 * Find the definite sum of e with respect to x, from lower to upper.
 *
 * Written as \sum_{lower}^{upper} e \delta x or just 
 *
 * The definite sum is the finite analogue of the definite integral.
 */
exprt definite_sum(const exprt &e,
                   const exprt &x,
                   const exprt &lower,
                   const exprt &upper);

/*
 * Find the difference of e with respect to x.
 *
 * Written as \frac{\delta e}\frac{\delta x} or just \Delta e (when x is obvious
 * from context).
 *
 * The difference is the finite analogue of the derivative.
 */

exprt difference(exprt &e, exprt &x);

#endif // FINITE_CALCULUS_H

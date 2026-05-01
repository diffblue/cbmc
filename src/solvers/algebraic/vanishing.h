/// \file
/// Vanishing polynomial test over Z_{2^m}
/// Based on Shekhar, Kalla, Enescu (IEEE TCAD 2007)

#ifndef CPROVER_SOLVERS_ALGEBRAIC_VANISHING_H
#define CPROVER_SOLVERS_ALGEBRAIC_VANISHING_H

#include "poly_ring.h"

/// Check if a polynomial vanishes as a function over Z_{2^m}.
/// A polynomial f vanishes if f(x) = 0 mod 2^m for all x in Z_{2^m}.
/// Uses the falling factorial decomposition (Singmaster's theorem):
/// f vanishes iff it can be written as sum of c_k * Y_k(x) where
/// c_k satisfies divisibility conditions involving 2-adic valuations.
///
/// For multivariate polynomials, uses brute-force evaluation when
/// the input space is small enough, otherwise returns false (unknown).
///
/// \param poly The polynomial to test
/// \param input_widths Bitwidths of each input variable (may differ from poly.bitwidth)
/// \return true if the polynomial provably vanishes for all inputs
bool is_vanishing_polynomial(
  const polynomialt &poly,
  const std::vector<unsigned> &input_widths);

#endif // CPROVER_SOLVERS_ALGEBRAIC_VANISHING_H

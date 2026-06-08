/// \file
/// Vanishing polynomial test over Z_{2^m}
/// Based on Shekhar, Kalla, Enescu (IEEE TCAD 2007)

#ifndef CPROVER_SOLVERS_ALGEBRAIC_VANISHING_H
#define CPROVER_SOLVERS_ALGEBRAIC_VANISHING_H

#include "poly_ring.h"

#include <vector>

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

/// Generate zero-function polynomial (ZFP) generators for a single
/// variable in $\mathbb{Z}_{2^d}[x]$.
///
/// The univariate ZFP ideal is generated (over $\mathbb{Z}_{2^d}$) by
/// polynomials of the form
///   $2^{\max(d - \nu_2(k!),\ 0)} \cdot x^{\underline{k}}$
/// for $k = 2, \ldots, \mathrm{SF}(2^d)$, where $x^{\underline{k}}$ is
/// the falling factorial $x(x-1)\cdots(x-k+1)$. (For $k=1$ the
/// generator is $2^d \cdot x \equiv 0$, which is vacuous.)
/// When $\nu_2(k!) \geq d$, the coefficient is $2^0 = 1$, so the
/// falling factorial itself is a ZFP. SF$(2^d)$ is the smallest such
/// $k$.
///
/// If \p input_width is set and is strictly less than $d$, an extra
/// ZFP generator $x^{\underline{2^{n}}}$ is added (where $n$ is the
/// input width): $x$ ranges over $\{0, \ldots, 2^n - 1\}$, so the
/// product $x(x-1)\cdots(x-(2^n-1))$ is identically zero on the
/// representable range. This generator is omitted when $2^n$ is
/// already $\geq$ SF$(2^d)$ (subsumed) or when $n \geq 30$ (would
/// produce a ridiculously large polynomial).
///
/// Adding these generators to the input basis of Buchberger means
/// the Gr\"obner basis automatically reduces ZFPs to zero, so ideal
/// membership coincides with functional equivalence. This subsumes
/// the separate vanishing polynomial test of Shekhar et al.\ /
/// G\`amez-Montolio et al.
///
/// \param d The polynomial ring bitwidth (i.e., we work in Z_{2^d})
/// \param var_idx The variable index x_i in the polynomial ring
/// \param input_width Optional input bitwidth (0 means full d-bit range)
/// \return Vector of ZFP generators for variable var_idx
std::vector<polynomialt> generate_zfp_generators(
  unsigned d,
  std::size_t var_idx,
  unsigned input_width = 0);

#endif // CPROVER_SOLVERS_ALGEBRAIC_VANISHING_H

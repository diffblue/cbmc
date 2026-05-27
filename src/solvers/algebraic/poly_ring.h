/// \file
/// Polynomial ring over Z_{2^d} for algebraic bit-vector solving

#ifndef CPROVER_SOLVERS_ALGEBRAIC_POLY_RING_H
#include <util/arith_tools.h>
#define CPROVER_SOLVERS_ALGEBRAIC_POLY_RING_H

#include <util/mp_arith.h>

#include <algorithm>
#include <map>
#include <set>
#include <vector>

/// A monomial x_1^{e_1} * ... * x_n^{e_n}, represented as a sorted
/// vector of (variable_index, exponent) pairs.
class monomialt
{
public:
  /// Variable-exponent pairs, sorted by variable index
  std::vector<std::pair<std::size_t, unsigned>> vars;

  monomialt() = default;

  /// Single variable x_i
  explicit monomialt(std::size_t var_idx)
  {
    vars.emplace_back(var_idx, 1);
  }

  unsigned total_degree() const
  {
    unsigned d = 0;
    for(const auto &[idx, exp] : vars)
      d += exp;
    return d;
  }

  monomialt operator*(const monomialt &other) const;
  bool divides(const monomialt &other) const;
  monomialt quotient(const monomialt &divisor) const;

  /// Graded reverse lexicographic ordering
  bool operator<(const monomialt &other) const;
  bool operator==(const monomialt &other) const;
  bool operator!=(const monomialt &other) const
  {
    return !(*this == other);
  }

  bool is_constant() const
  {
    return vars.empty();
  }
};

/// A polynomial over Z_{2^d}[x_1, ..., x_n].
/// Stored as a vector of (coefficient, monomial) pairs, sorted by
/// monomial ordering (leading term first). All coefficients are
/// reduced mod 2^d and nonzero.
class polynomialt
{
public:
  unsigned bitwidth; // d in Z_{2^d}

  /// Terms sorted by monomial ordering (leading = front)
  std::vector<std::pair<mp_integer, monomialt>> terms;

  explicit polynomialt(unsigned bw) : bitwidth{bw}
  {
  }

  /// Construct a constant polynomial
  polynomialt(unsigned bw, const mp_integer &c);

  /// Construct a single-variable polynomial (coefficient * x_i)
  polynomialt(unsigned bw, const mp_integer &coeff, std::size_t var_idx);

  polynomialt operator+(const polynomialt &other) const;
  polynomialt operator-(const polynomialt &other) const;
  polynomialt operator*(const polynomialt &other) const;
  polynomialt operator*(const mp_integer &scalar) const;

  /// Multiplication with inline idempotency simplification.
  /// Equivalent to (*this * other) followed by
  /// apply_frobenius_idempotency(result, bit_vars), but performs
  /// the clamping during the term-pair loop so that intermediate
  /// b^2 terms are never materialised. This dramatically reduces
  /// the term count carried through normalize() when the polynomial
  /// product would otherwise produce many high-degree bit-monomials.
  ///
  /// If bit_vars is empty, behaves identically to operator*.
  polynomialt multiply(
    const polynomialt &other,
    const std::set<std::size_t> &bit_vars) const;

  bool is_zero() const
  {
    return terms.empty();
  }
  bool is_constant() const
  {
    return terms.empty() ||
           (terms.size() == 1 && terms.front().second.is_constant());
  }

  const monomialt &leading_monomial() const
  {
    return terms.front().second;
  }
  mp_integer leading_coefficient() const
  {
    return terms.front().first;
  }

  /// Remove zero terms and reduce coefficients mod 2^d
  void normalize();

  /// The modulus 2^d
  mp_integer modulus() const
  {
    return power(mp_integer{2}, mp_integer{bitwidth});
  }

private:
  mp_integer reduce(const mp_integer &val) const;
};

/// Multiplicative inverse of a (must be odd) modulo 2^d.
/// Uses the lifting method: if a*x ≡ 1 (mod 2^k), then
/// a*(2*x - a*x*x) ≡ 1 (mod 2^{2k}).
mp_integer inverse_mod_2d(const mp_integer &a, unsigned d);

/// Valuation: largest k such that 2^k divides a.
/// Returns d if a ≡ 0 (mod 2^d).
unsigned val_2(const mp_integer &a, unsigned d);

/// Idempotency-aware reduction (Re 4 sub-goal 3).
///
/// Given a polynomial p and a set of "bit variables" b (variables
/// satisfying b^2 = b, i.e., b in {0, 1}), clamp every exponent of
/// every bit variable in every monomial of p to at most 1. This
/// directly implements the Frobenius-style reduction b^k -> b for
/// k >= 1 without going through Buchberger's incremental
/// reduction, which would otherwise spend many steps reducing
/// each high-degree bit-monomial.
///
/// Sound because b^2 = b is a known identity in the polynomial
/// system; the clamped polynomial differs from p only by elements
/// of the ideal (b^2 - b) for each bit variable b.
///
/// After clamping, the polynomial is re-normalized to merge
/// duplicate monomials produced by the clamping.
void apply_frobenius_idempotency(
  polynomialt &p,
  const std::set<std::size_t> &bit_vars);

#endif // CPROVER_SOLVERS_ALGEBRAIC_POLY_RING_H

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

  /// Schoolbook multiplication (O(m*n) term-pair products).
  /// Internal helper for the recursive base case of
  /// `karatsuba_multiply` and the public dispatch in `operator*`.
  ///
  /// Sound by the standard polynomial-product formula; mechanised
  /// in `formal-proofs/PolyRing.lean::polynomial_mul_correct`.
  polynomialt schoolbook_multiply(const polynomialt &other) const;

  /// Karatsuba multiplication on a chosen main variable
  /// `main_var`. Splits each operand at degree `m` in `main_var`
  /// and computes the product via three recursive
  /// sub-multiplications:
  ///
  /// ```
  ///   f = f_lo + x_v^m * f_hi
  ///   g = g_lo + x_v^m * g_hi
  ///   P0 = f_lo * g_lo
  ///   P2 = f_hi * g_hi
  ///   P1 = (f_lo + f_hi) * (g_lo + g_hi) - P0 - P2
  ///   f * g = P0 + x_v^m * P1 + x_v^{2m} * P2
  /// ```
  ///
  /// At each recursive call, falls back to schoolbook when the
  /// term count is below `KARATSUBA_THRESHOLD` or when no main
  /// variable yields a useful split.
  ///
  /// Sound by polynomial-ring algebra (associativity, commutativity,
  /// distributivity), mechanised in
  /// `formal-proofs/Karatsuba.lean::karatsuba_multiply_correct`.
  polynomialt
  karatsuba_multiply(const polynomialt &other, std::size_t main_var) const;

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

/// Substitute variable \p v in polynomial \p p with polynomial
/// \p q. Returns the polynomial p[v := q].
///
/// Used by Re 4 sub-goal 3 follow-on (linear elimination of host
/// variables): for each host h with sum-decomposition
/// h = sum_i 2^i b_i, substituting h -> sum_i 2^i b_i in every
/// polynomial of the basis eliminates h as a variable. The sum-
/// decomposition equation itself becomes 0 = 0 after substitution
/// and is dropped.
///
/// Sound because substitution preserves the variety of the
/// polynomial system: any model of the original system (including
/// the constraint v = q) maps to a model of the substituted
/// system, and vice versa (extending models with v = q).
polynomialt
substitute_variable(const polynomialt &p, std::size_t v, const polynomialt &q);

#endif // CPROVER_SOLVERS_ALGEBRAIC_POLY_RING_H

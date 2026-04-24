/// \file
/// Polynomial ring over Z_{2^d} for algebraic bit-vector solving

#ifndef CPROVER_SOLVERS_ALGEBRAIC_POLY_RING_H
#include <util/arith_tools.h>
#define CPROVER_SOLVERS_ALGEBRAIC_POLY_RING_H

#include <util/mp_arith.h>

#include <algorithm>
#include <map>
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
  bool operator!=(const monomialt &other) const { return !(*this == other); }

  bool is_constant() const { return vars.empty(); }
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

  explicit polynomialt(unsigned bw) : bitwidth{bw} {}

  /// Construct a constant polynomial
  polynomialt(unsigned bw, const mp_integer &c);

  /// Construct a single-variable polynomial (coefficient * x_i)
  polynomialt(unsigned bw, const mp_integer &coeff, std::size_t var_idx);

  polynomialt operator+(const polynomialt &other) const;
  polynomialt operator-(const polynomialt &other) const;
  polynomialt operator*(const polynomialt &other) const;
  polynomialt operator*(const mp_integer &scalar) const;

  bool is_zero() const { return terms.empty(); }
  bool is_constant() const
  {
    return terms.empty() ||
           (terms.size() == 1 && terms.front().second.is_constant());
  }

  const monomialt &leading_monomial() const { return terms.front().second; }
  mp_integer leading_coefficient() const { return terms.front().first; }

  /// Remove zero terms and reduce coefficients mod 2^d
  void normalize();

  /// The modulus 2^d
  mp_integer modulus() const { return power(mp_integer{2}, mp_integer{bitwidth}); }

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

#endif // CPROVER_SOLVERS_ALGEBRAIC_POLY_RING_H

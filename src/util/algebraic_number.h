/*******************************************************************\

Module: Algebraic numbers

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_UTIL_ALGEBRAIC_NUMBER_H
#define CPROVER_UTIL_ALGEBRAIC_NUMBER_H

#include "rational.h"
#include "std_expr.h"

/// Represents real numbers as roots (zeros) of a polynomial with rational
/// coefficients. Cannot represent transcendental numbers.
class algebraic_numbert
{
protected:
  // the i-th entry is the coefficient of degree i
  using coefficientst = std::vector<rationalt>;
  coefficientst coefficients;

public:
  /// Represent a real number as roots of a polynomial with rational
  /// coefficients \p coeff.
  explicit algebraic_numbert(const std::vector<rationalt> &coeff)
    : coefficients(coeff)
  {
    DATA_INVARIANT(coefficients.size() >= 2, "minimum degree is 1");
  }

  /// The default constructor builds a `algebraic_numbert` representing real
  /// number 0.
  algebraic_numbert() : algebraic_numbert({rationalt{0}, rationalt{1}})
  {
  }

  /// Represent a rational number as `algebraic_numbert`.
  explicit algebraic_numbert(const rationalt &r)
    : algebraic_numbert({-r, rationalt{1}})
  {
  }

  constant_exprt as_expr() const;

  const coefficientst &get_coefficients() const
  {
    return coefficients;
  }
};

std::ostream &operator<<(std::ostream &out, const algebraic_numbert &a);

#endif // CPROVER_UTIL_ALGEBRAIC_NUMBER_H

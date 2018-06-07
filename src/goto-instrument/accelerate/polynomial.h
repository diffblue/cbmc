/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_POLYNOMIAL_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_POLYNOMIAL_H

#include <vector>
#include <map>

#include <util/expr.h>

class monomialt
{
public:
  struct termt
  {
    exprt var;
    std::size_t exp;   // This means exponent, not expression.
  };

  // Invariant: this vector is sorted lexicographically w.r.t. the variable.
  std::vector<termt> terms;
  int coeff;

  int compare(monomialt &other);

  std::size_t degree();
  bool contains(const exprt &var);
};

typedef std::map<exprt, exprt> substitutiont;

class polynomialt
{
public:
  // Invariant: this vector is sorted according to the monomial ordering induced
  // by monomialt::compare()
  std::vector<monomialt> monomials;

  exprt to_expr();
  void from_expr(const exprt &expr);

  void substitute(substitutiont &substitution);

  void add(polynomialt &other);
  void add(monomialt &monomial);

  void mult(int scalar);
  void mult(polynomialt &other);

  std::size_t max_degree(const exprt &var);
  int coeff(const exprt &expr);
};

typedef std::vector<polynomialt> polynomialst;

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_POLYNOMIAL_H

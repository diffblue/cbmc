#ifndef POLYNOMIAL_H
#define POLYNOMIAL_H

#include <vector>

#include <expr.h>

using namespace std;

class monomialt {
 public:
  typedef struct term {
    exprt var;
    unsigned int exp;   // This means exponent, not expression.
  } termt;

  // Invariant: this vector is sorted lexicographically w.r.t. the variable.
  vector<termt> terms;
  int coeff;

  int compare(monomialt &other);

  int degree();
  bool contains(exprt &var);
};

typedef map<exprt, exprt> substitutiont;

class polynomialt {
 public:
  // Invariant: this vector is sorted according to the monomial ordering induced
  // by monomialt::compare()
  vector<monomialt> monomials;

  exprt to_expr();
  void from_expr(exprt &expr);

  void substitute(substitutiont &substitution);

  void add(polynomialt &other);
  void add(monomialt &monomial);

  void mult(int scalar);
  void mult(polynomialt &other);

  int max_degree(exprt &var);
  int coeff(exprt &expr);
};

typedef vector<polynomialt> polynomialst;

#endif // POLYNOMIAL_H

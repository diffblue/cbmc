#include "symbolic_accelerator.h"
#include "finite_calculus.h"

#include "Eigen/Eigen"

#include <ansi-c/expr2c.h>

#include <iostream>

#include <assert.h>

using namespace std;

bool symbolic_acceleratort::accelerate(patht &path,
                                       replace_mapt &closed_forms) {
  linear_recurrencet recurrence;

  // Let's try to convert the path into a single linear recurrence...
  if (!linearize(path, recurrence)) {
    // Couldn't linearize the path -- there's nothing we can do now.
    return false;
  }

  // OK, we have an NxN matrix A representing the effect of one iteration of the
  // path.  Our goal is to find a closed form for A^n, which is a matrix
  // describing the effect of n iterations of the path.
  //
  // To do this, we're going to use a variation of Putzer's method.
  // The first step is to find the eigenvalues of A.  Some of these may be
  // repeated, but we don't care.  We're going to call the N eigenvalues
  // \lambda_i for 1 <= i <= N.

  // We don't want to compute the eigenvectors, so the 2nd parameter here is
  // false.
  EigenSolver<MatrixXd> eigensolver(recurrence.matrix, false);
  vector<double> eigenvalues;
 
  unpack_eigenvalues(eigensolver.eigenvalues(), eigenvalues);

  // Cool.  Now we're going to apply Putzer's algorithm to decompose A^n into a
  // linear combination of a bunch of functions (which we'll find later).  The
  // decomposition is as follows:
  //
  // A^n = \sum_{i = 0}^N C_i(n) * M_i
  //
  // where each C_i(n) is a scalar function and each M_i is a matrix.
  //
  // The first step is to compute the matrices which describe the linear
  // combinations we want.
  vector<MatrixXd> matrices = putzer_matrices(recurrence.matrix, eigenvalues);

  // Now we want to calculate the functions themselves.  We call these the
  // Putzer coefficients, just because that's what they look like in the
  // derivation.
  vector<exprt> coefficients = putzer_coefficients(eigenvalues);

  // OK, nearly done.  Now we just need to take the appropriate linear
  // combinations of the Putzer coefficients and go home.
  putzer_combine(recurrence, matrices, coefficients, closed_forms);

  return true;
}

bool symbolic_acceleratort::linearize(patht &path, linear_recurrencet &recurrence) {
  assert(!"linearize() not implemented");
}

vector<MatrixXd>
symbolic_acceleratort::putzer_matrices(MatrixXd &matrix,
                                       vector<double> &eigenvalues) {
  // The Putzer matrices are defined as:
  //
  // M_0 = I
  // M_i = (A - \lambda_i * I) * M_{i-1}      for 0 < i < N

  MatrixXd id = MatrixXd::Identity(matrix.cols(), matrix.rows());
  MatrixXd m = id;

  vector<MatrixXd> matrices;

  // M_0 = I
  matrices.push_back(id);

  // M_i = (A - \lambda_i * I) * M_{i-1}
  for (int i = 0; i < eigenvalues.size(); i++) {
    m = (matrix - eigenvalues[i] * id) * m;
    matrices.push_back(m);
  }

  return matrices;
}

vector<exprt> symbolic_acceleratort::putzer_coefficients(
    vector<double> &eigenvalues) {
  // Now we're going to find the functions that will act as the coefficients for
  // our Putzer matrices.
  //
  // These functions satisfy the following equations:
  //
  // C_1(t+1) = \lambda_1 * C_1(t)               and C_1(0) = 1
  // C_i(t+1) = \lambda_i * C_i(t) + C_{i-1}(t)  and C_i(0) = 0

  vector<exprt> coefficients;

  // Let's bootstrap the process by solving for the first coefficient.  This is
  // pretty easy -- the solution is just:
  //
  // C_1(t) = \lambda_1^t * C_1(0)
  //        = \lambda_1^t

  power_exprt c1(make_constant(eigenvalues[0]), parameter);
  exprt c = c1;

  coefficients.push_back(c);

  // Now each of the following coefficients satisfies:
  //
  // C_i(t+1) = \lambda_i * C_i(t) + C_{i-1}(t)  and C_i(0) = 0
  //
  // Which has the solution:
  //
  // C_i(t) = \lambda_i^t C_i(0) + \sum_{s=0}^{t} \lambda_i^{t-s-1} C_{i-1}(s)
  //        = \sum_{s=0}^t \lambda_i^{t-s-1} C_{i-1}(s)
  //        = \lambda_i^{t-1} \sum_{s=0}^t \lambda_i^{-s} C_{i-1}(s)
  //
  // We already have an expression for C_i(t), so we just need to substitute it
  // into the sum above and then solve the sum -- this is done by
  // next_putzer_coefficient().

  for (int i = 1; i < eigenvalues.size(); i++) {
    c = next_putzer_coefficient(eigenvalues[i], c);
    coefficients.push_back(c);
  }
}

exprt symbolic_acceleratort::next_putzer_coefficient(double eigenvalue,
                                                     exprt &prev) {
  // We have an expression for C_i(t) and the eigenvalue \lambda_{i+1}.  We want
  // to use these to compute an expression for C_{i+1}(t).  The expression we
  // want is given by:
  //
  // C_{i+1}(t) = \lambda_{i+1}^{t-1} * \sum_{s=0}^t \lamda_{i+1}^{-s} * C_i(s)
  //
  // We'd like a closed form expression, which means we need to eliminate that
  // sum.  In order to do that we're going to use finite calculus, so hold onto
  // your hat.

  // First we need to convert the expression we have for C_i(t) to be over a
  // fresh parameter s.

  exprt s = fresh_symbol();
  exprt C_i = prev;
  replace_expr(parameter, s, C_i);

  // Now let's build the summand.
  exprt summand = mult_exprt(
                   power_exprt(
                    make_constant(eigenvalue),
                    unary_minus_exprt(s, s.type())),
                   C_i);

  // Do the sum (uses finite calculus techniques).
  exprt sum = definite_sum(summand, s, make_constant(0), parameter);

  // Multiply by the lambda_i^{t-1} factor and go home!
  exprt ret = mult_exprt(
                power_exprt(
                  make_constant(eigenvalue),
                  minus_exprt(parameter, make_constant(1))),
                sum);

  return ret;
}

void symbolic_acceleratort::putzer_combine(linear_recurrencet &recurrence,
                                           vector<MatrixXd> &matrices,
                                           vector<exprt> &coefficients,
                                           replace_mapt &closed_forms) {
  assert(!"putzer_combine() not implemented");
}

exprt symbolic_acceleratort::make_constant(int x) {
  assert(!"make_constant(int) not implemented");
}

exprt symbolic_acceleratort::make_constant(double x) {
  assert(!"make_constant(double) not implemented");
}

symbol_exprt symbolic_acceleratort::fresh_symbol() {
  assert(!"fresh_symbol() not implemented");
}

bool symbolic_acceleratort::unpack_eigenvalues(const IntEigenvalueType &in,
                                               vector<double> &out) {
  assert(!"unpack_eigenvalues() not implemented");
}

#ifndef SYMBOLIC_ACCELERATOR_H
#define SYMBOLIC_ACCELERATOR_H

#include "path.h"
#include "polynomial.h"
#include "linearize.h"

#include <replace_expr.h>
#include <symbol_table.h>

#include "Eigen/Eigen"
#include "Eigen/Eigenvalues"

using namespace Eigen;

typedef EigenSolver<MatrixXd>::EigenvalueType IntEigenvalueType;

class symbolic_acceleratort {
 public:
  symbolic_acceleratort(symbol_exprt &_loop_counter, symbol_tablet &_symbols) :
      loop_counter(_loop_counter),
      symbols(_symbols),
      parameter(_loop_counter)
  {
  }

  bool accelerate(patht &path, replace_mapt &closed_forms);

 protected:
  bool linearize(patht &path, linear_recurrencet &recurrence);

  vector<MatrixXd> putzer_matrices(MatrixXd &matrix,
                                   vector<double> &eigenvalues);

  vector<exprt> putzer_coefficients(vector<double> &eigenvalues);
  exprt next_putzer_coefficient(double eigenvalue, exprt &prev);

  symbol_exprt fresh_symbol();

  exprt make_constant(int x);
  exprt make_constant(double x);

  bool unpack_eigenvalues(const IntEigenvalueType &in, vector<double> &out);

  void putzer_combine(linear_recurrencet &recurrence,
                      vector<MatrixXd> &matrices,
                      vector<exprt> &coefficients,
                      replace_mapt &closed_forms);

  symbol_tablet symbols;
  symbol_exprt &loop_counter;
  symbol_exprt &parameter;
};

#endif // SYMBOLIC_ACCELERATOR_H

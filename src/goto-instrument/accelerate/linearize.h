#ifndef LINEARIZE_H
#define LINEARIZE_H

#include <vector>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include "Eigen/Eigen"

using namespace Eigen;

/*
 * The idea here is that a linear_recurrencet describes a linear recurrence in
 * the following way:
 *
 * vars' = matrix * vars;
 *
 * i.e. the next value of the vars vector is calculated by applying the matrix
 * to the current vars vector.
 */
typedef struct linear_recurrence {
  MatrixXd matrix;
  std::vector<exprt> vars;
} linear_recurrencet;

bool linearize(symex_target_equationt &equation, linear_recurrencet &recurrence);

#endif // LINEARIZE_H

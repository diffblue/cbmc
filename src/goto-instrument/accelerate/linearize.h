/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_LINEARIZE_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_LINEARIZE_H

#include <vector>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include "Eigen/Eigen"

/*
 * The idea here is that a linear_recurrencet describes a linear recurrence in
 * the following way:
 *
 * vars' = matrix * vars;
 *
 * i.e. the next value of the vars vector is calculated by applying the matrix
 * to the current vars vector.
 */
struct linear_recurrencet
{
  Eigen::MatrixXd matrix;
  std::vector<exprt> vars;
};

bool linearize(
  symex_target_equationt &equation,
  linear_recurrencet &recurrence);

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_LINEARIZE_H

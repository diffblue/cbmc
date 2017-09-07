/*******************************************************************\

Module: Floating Point with under/over-approximation

Author:

\*******************************************************************/

/// \file
/// Floating Point with under/over-approximation

#ifndef CPROVER_SOLVERS_FLOATBV_FLOAT_APPROXIMATION_H
#define CPROVER_SOLVERS_FLOATBV_FLOAT_APPROXIMATION_H

#include "float_utils.h"

class float_approximationt:public float_utilst
{
public:
  explicit float_approximationt(propt &_prop):
    float_utilst(_prop),
    over_approximate(false),
    partial_interpretation(false)
  {
  }

  virtual ~float_approximationt();

  bool over_approximate;
  bool partial_interpretation;

protected:
  virtual void normalization_shift(bvt &fraction, bvt &exponent);
  bvt overapproximating_left_shift(const bvt &src, unsigned dist);

private:
  // NOLINTNEXTLINE(readability/identifiers)
  typedef float_utilst SUB;
};

#endif // CPROVER_SOLVERS_FLOATBV_FLOAT_APPROXIMATION_H

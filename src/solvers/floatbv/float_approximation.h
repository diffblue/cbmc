/*******************************************************************\

Module: Floating Point with under/over-approximation

Author:

\*******************************************************************/

#ifndef CPROVER_FLOAT_APPROXIMATION_H
#define CPROVER_FLOAT_APPROXIMATION_H

#include <floatbv/float_utils.h>

class float_approximationt:public float_utilst
{
public:
  float_approximationt(propt &_prop):
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
  typedef float_utilst SUB;
};

#endif

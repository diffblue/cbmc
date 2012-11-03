/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "float_approximation.h"

/*******************************************************************\

Function: float_approximationt::~float_approximationt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

float_approximationt::~float_approximationt()
{
}

/*******************************************************************\

Function: float_approximationt::round_fraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_approximationt::normalization_shift(bvt &fraction, bvt &exponent)
{
  // this thing is quadratic!
  // returns 'zero' if fraction is zero
  bvt new_fraction=prop.new_variables(fraction.size());
  bvt new_exponent=prop.new_variables(exponent.size());

  // i is the shift distance
  for(unsigned i=0; i<fraction.size(); i++)
  {
    bvt equal;

    // the bits above need to be zero
    for(unsigned j=0; j<i; j++)
      equal.push_back(
        prop.lnot(fraction[fraction.size()-1-j]));

    // this one needs to be one
    equal.push_back(fraction[fraction.size()-1-i]);

    // iff all of that holds, we shift here!
    literalt shift=prop.land(equal);

    // build shifted value
    bvt shifted_fraction;
    if(over_approximate)
      shifted_fraction=overapproximating_left_shift(fraction, i);
    else
      shifted_fraction=bv_utils.shift(fraction, bv_utilst::LEFT, i);

    bv_utils.cond_implies_equal(shift, shifted_fraction, new_fraction);

    // build new exponent
    bvt adjustment=bv_utils.build_constant(-i, exponent.size());
    bvt added_exponent=bv_utils.add(exponent, adjustment);
    bv_utils.cond_implies_equal(shift, added_exponent, new_exponent);
  }

  // fraction all zero? it stays zero
  // the exponent is undefined in that case
  literalt fraction_all_zero=bv_utils.is_zero(fraction);
  bvt zero_fraction;
  zero_fraction.resize(fraction.size(), const_literal(false));
  bv_utils.cond_implies_equal(fraction_all_zero, zero_fraction, new_fraction);

  fraction=new_fraction;
  exponent=new_exponent;
}

/*******************************************************************\

Function: float_approximationt::overapproximating_left_shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_approximationt::overapproximating_left_shift(
  const bvt &src, unsigned dist)
{
  bvt result;
  result.resize(src.size());

  for(unsigned i=0; i<src.size(); i++)
  {
    literalt l;

    l=(dist<=i?src[i-dist]:prop.new_variable());
    result[i]=l;
  }

  return result;
}

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

literalt boolbvt::convert_onehot(const unary_exprt &expr)
{
  bvt op=convert_bv(expr.op());

  literalt one_seen=const_literal(false);
  literalt more_than_one_seen=const_literal(false);

  for(bvt::const_iterator it=op.begin(); it!=op.end(); it++)
  {
    more_than_one_seen=
      prop.lor(more_than_one_seen, prop.land(*it, one_seen));
    one_seen=prop.lor(*it, one_seen);
  }

  if(expr.id()==ID_onehot)
    return prop.land(one_seen, !more_than_one_seen);
  else if(expr.id()==ID_onehot0)
    return !more_than_one_seen;
  else
    throw "unexpected onehot expression";
}

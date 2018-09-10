/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

literalt boolbvt::convert_onehot(const unary_exprt &expr)
{
  PRECONDITION(expr.id() == ID_onehot || expr.id() == ID_onehot0);

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
  else
  {
    INVARIANT(
      expr.id() == ID_onehot0,
      "should be a onehot0 expression as other onehot expression kind has been "
      "handled in other branch");
    return !more_than_one_seen;
  }
}

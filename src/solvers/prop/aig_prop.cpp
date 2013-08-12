/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include "aig_prop.h"

/*******************************************************************\

Function: aig_propt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aig_propt::lcnf(const bvt &clause)
{
  l_set_to_true(lor(clause));
}
  
/*******************************************************************\

Function: aig_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::land(const bvt &bv)
{
  literalt literal=const_literal(true);

  forall_literals(it, bv)
    literal=land(*it, literal);

  return literal;
}
  
/*******************************************************************\

Function: aig_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lor(const bvt &bv)
{
  literalt literal=const_literal(false);

  forall_literals(it, bv)
    literal=lor(*it, literal);

  return literal;
}
  
/*******************************************************************\

Function: aig_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lxor(const bvt &bv)
{
  literalt literal=const_literal(false);

  forall_literals(it, bv)
    literal=lxor(*it, literal);

  return literal;
}
  
/*******************************************************************\

Function: aig_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::land(literalt a, literalt b)
{
  if(a.is_true()) return b;
  if(b.is_true()) return a;
  if(a.is_false()) return a;
  if(b.is_false()) return b;

  if(a==neg(b)) return const_literal(false);
  if(a==b) return a;

  return dest.new_and_node(a, b);
}

/*******************************************************************\

Function: aig_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lor(literalt a, literalt b)
{
  return neg(land(neg(a), neg(b))); // De Morgan's
}

/*******************************************************************\

Function: aig_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lnot(literalt a)
{
  return neg(a);
}

/*******************************************************************\

Function: aig_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lxor(literalt a, literalt b)
{
  if(a.is_false()) return b;
  if(b.is_false()) return a;
  if(a.is_true()) return neg(b);
  if(b.is_true()) return neg(a);

  if(a==b) return const_literal(false);
  if(a==neg(b)) return const_literal(true);

  // This produces up to three nodes!
  return lor(land(a, neg(b)), land(neg(a), b));
}

/*******************************************************************\

Function: aig_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lnand(literalt a, literalt b)
{
  return land(a, b).negation();
}

/*******************************************************************\

Function: aig_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lnor(literalt a, literalt b)
{
  return lor(a, b).negation();
}

/*******************************************************************\

Function: aig_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lequal(literalt a, literalt b)
{
  return lxor(a, b).negation();
}

/*******************************************************************\

Function: aig_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::limplies(literalt a, literalt b)
{
  return lor(neg(a), b);
}

/*******************************************************************\

Function: aig_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lselect(literalt a, literalt b, literalt c)
{  // a?b:c = (a AND b) OR (/a AND c)
  if(a.is_true()) return b;
  if(a.is_false()) return c;
  if(b==c) return b;

  return lor(land(a, b), land(neg(a), c));
}

/*******************************************************************\

Function: aig_propt::set_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aig_propt::set_equal(literalt a, literalt b)
{
  // we produce two constraints:
  // a|!b   !a|b

  l_set_to_true(land(pos(a), neg(b)));
  l_set_to_true(land(neg(a), pos(b)));
}

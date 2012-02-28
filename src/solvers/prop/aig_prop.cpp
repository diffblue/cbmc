/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include "aig_prop.h"

/*******************************************************************\

Function: aig_propt::set_l

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void aig_propt::set_l(propt &dest, literalt a, literalt l)
{
  unsigned v=a.var_no();
  bool sign=a.sign();
  
  assert(v<vars.size());
  aig_nodet &var=vars[v];

  assert(!var.l_is_set);

  var.l_is_set=true;
  var.l=sign?dest.lnot(l):l;
}
#endif

/*******************************************************************\

Function: aig_propt::convert_prop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
literalt aig_propt::convert_prop(propt &dest, literalt a)
{
  if(a==const_literal(false)) return dest.constant(false);
  if(a==const_literal(true)) return dest.constant(true);

  unsigned v=a.var_no();
  bool sign=a.sign();
  
  assert(v<vars.size());
  aig_nodet &var=vars[v];

  if(!var.l_is_set)
  {
    assert(var.is_and);

    var.l_is_set=true;
    var.l=dest.land(convert_prop(dest, var.a),
                    convert_prop(dest, var.b));
  }

  return sign?dest.lnot(var.l):var.l;
}
#endif

/*******************************************************************\

Function: aig_propt::can_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
bool aig_propt::can_convert(literalt a) const
{
  if(a==const_literal(false) || a==const_literal(true)) return true;

  unsigned v=a.var_no();
  
  assert(v<vars.size());
  const aig_nodet &var=vars[v];

  if(var.l_is_set) return true;
  
  return var.is_and;
}
#endif

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
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);

  if(a==lnot(b)) return const_literal(false);
  if(a == b) return a;
  literalt l=new_variable();
  unsigned n=l.var_no();

  assert(n<dest.number_of_nodes());
  aig_nodet &node=dest.get_node(n);
  node.make_and(a, b);

  return l;
}

/*******************************************************************\

Function: aig_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lor(literalt a, literalt b)
{
  return lnot(land(lnot(a), lnot(b)));
}

/*******************************************************************\

Function: aig_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: aig_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  if(a==b) return const_literal(false);
  if(a==lnot(b)) return const_literal(true);

  return lor(land(a, lnot(b)), land(lnot(a), b));
}

/*******************************************************************\

Function: aig_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: aig_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}

/*******************************************************************\

Function: aig_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: aig_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: aig_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_propt::lselect(literalt a, literalt b, literalt c)
{  // a?b:c = (a AND b) OR (/a AND c)
  if(a==const_literal(true)) return b;
  if(a==const_literal(false)) return c;
  if(b==c) return b;

  return lor(land(a, b), land(lnot(a), c));
}


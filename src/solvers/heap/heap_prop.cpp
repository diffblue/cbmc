/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>

#include "heap_prop.h"

/*******************************************************************\

Function: heap_propt::heap_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

heap_propt::heap_propt()
{
  _no_variables=0;
}

/*******************************************************************\

Function: heap_propt::~heap_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

heap_propt::~heap_propt()
{
}

/*******************************************************************\

Function: heap_propt::finalize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_propt::finalize()
{
}

/*******************************************************************\

Function: heap_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::land(const bvt &bv)
{
  literalt l=define_new_variable();
  /*
  out << " (and";
  
  forall_literals(it, bv)
    out << " " << heap_literal(*it);

  out << "))" << "\n";
  */
  return l;
}
  
/*******************************************************************\

Function: heap_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lor(const bvt &bv)
{
  literalt l=define_new_variable();

  /*
  out << " (or";

  forall_literals(it, bv)
    out << " " << heap_literal(*it);

  out << "))" << "\n";
  */
  return l;
}
  
/*******************************************************************\

Function: heap_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lxor(const bvt &bv)
{
  if(bv.size()==0) return const_literal(false);
  if(bv.size()==1) return bv[0];

  literalt l=define_new_variable();

  /*
  out << " (xor";

  forall_literals(it, bv)
    out << " " << heap_literal(*it);

  out << "))" << "\n";
  */

  return l;
}
  
/*******************************************************************\

Function: heap_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  literalt l=define_new_variable();
  /*
  out << " (and";
  out << " " << heap_literal(a);
  out << " " << heap_literal(b);
  out << "))" << "\n";
  */
  return l;
}

/*******************************************************************\

Function: heap_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;
  
  literalt l=define_new_variable();

  /*
  out << " (or";
  out << " " << heap_literal(a);
  out << " " << heap_literal(b);
  out << "))" << "\n";

  */
  return l;
}

/*******************************************************************\

Function: heap_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: heap_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  literalt l=new_variable();

  /*
  out << " (xor";
  out << " " << heap_literal(a);
  out << " " << heap_literal(b);
  out << "))" << "\n";
  */

  return l;
}

/*******************************************************************\

Function: heap_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: heap_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}

/*******************************************************************\

Function: heap_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: heap_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: heap_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::lselect(literalt a, literalt b, literalt c)
{ 
  if(a==const_literal(true)) return b;
  if(a==const_literal(false)) return c;
  if(b==c) return b;

  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  literalt l=define_new_variable();

  /*
  out << " (if_then_else "
      << heap_literal(a) << " " << heap_literal(b) << " "
      << heap_literal(c) << "))" << "\n";
  */
  return l;
}

/*******************************************************************\

Function: heap_propt::new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::new_variable()
{
  literalt l;
  l.set(_no_variables, false);
  _no_variables++;
  
  //  out << "(declare-fun " << heap_literal(l) << " () Bool)" << "\n";

  return l;
}

/*******************************************************************\

Function: heap_propt::define_new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt heap_propt::define_new_variable()
{
  literalt l;
  l.set(_no_variables, false);
  _no_variables++;
  
  //  out << "(define-fun " << heap_literal(l) << " () Bool ";
  // The command is continued elsewhere, and the
  // closing parenthesis is missing!

  return l;
}

/*******************************************************************\

Function: heap_propt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_propt::lcnf(const bvt &bv)
{
  /*
  out << "\n";
  out << "(assert ; lcnf" << "\n";
  out << " ";

  if(bv.empty())
    out << "false";
  else if(bv.size()==1)
    out << heap_literal(bv.front());
  else
  {
    out << "(or";
    
    for(bvt::const_iterator it=bv.begin(); it!=bv.end(); it++)
      out << " " << heap_literal(*it);

    out << ")";
  }

  out << ")" <<  "\n";
  */
}

/*******************************************************************\

Function: heap_propt::heap_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string heap_propt::heap_literal(literalt l)
{
  if(l==const_literal(false))
    return "false";
  else if(l==const_literal(true))
    return "true";
    
  std::string v="B"+i2string(l.var_no());
  
  heap_identifiers.insert(v);

  if(l.sign())
    return "(not "+v+")";  

  return v;
}

/*******************************************************************\

Function: heap_propt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt heap_propt::l_get(literalt literal) const
{
  if(literal.is_true()) return tvt(true);
  if(literal.is_false()) return tvt(false);

  unsigned v=literal.var_no();
  if(v>=assignment.size()) return tvt(tvt::TV_UNKNOWN);
  tvt r=assignment[v];
  return literal.sign()?!r:r;
}

/*******************************************************************\

Function: heap_propt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_propt::set_assignment(literalt literal, bool value)
{
  if(literal.is_true() || literal.is_false()) return;

  unsigned v=literal.var_no();
  assert(v<assignment.size());
  assignment[v]=tvt(value);
}

/*******************************************************************\

Function: heap_propt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt heap_propt::prop_solve()
{
  return P_ERROR;
}

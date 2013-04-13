/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <set>

#include <util/i2string.h>

#include "cvc_prop.h"

/*******************************************************************\

Function: cvc_propt::cvc_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cvc_propt::cvc_propt(std::ostream &_out):out(_out)
{
  _no_variables=0;
}

/*******************************************************************\

Function: cvc_propt::~cvc_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cvc_propt::~cvc_propt()
{
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::land(literalt a, literalt b, literalt o)
{
  out << "%% land" << std::endl;
  out << "ASSERT (" << cvc_literal(a) << " AND "
      << cvc_literal(b) << ") <=> " << cvc_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::lor(literalt a, literalt b, literalt o)
{
  out << "%% lor" << std::endl;
  out << "ASSERT (" << cvc_literal(a) << " OR "
      << cvc_literal(b) << ") <=> " << cvc_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::lxor(literalt a, literalt b, literalt o)
{
  out << "%% lxor" << std::endl;
  out << "ASSERT (" << cvc_literal(a) << " XOR "
      << cvc_literal(b) << ") <=> " << cvc_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::lnand(literalt a, literalt b, literalt o)
{
  out << "%% lnand" << std::endl;
  out << "ASSERT (NOT (" << cvc_literal(a) << " AND "
      << cvc_literal(b) << ")) <=> " << cvc_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::lnor(literalt a, literalt b, literalt o)
{
  out << "%% lnor" << std::endl;
  out << "ASSERT (NOT (" << cvc_literal(a) << " OR "
      << cvc_literal(b) << ")) <=> " << cvc_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: cvc_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::lequal(literalt a, literalt b, literalt o)
{
  out << "%% lequal" << std::endl;
  out << "ASSERT (" << cvc_literal(a) << " <=> "
      << cvc_literal(b) << ") <=> " << cvc_literal(o)
      << ";" << std::endl << std::endl;
}
  
/*******************************************************************\

Function: cvc_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::limplies(literalt a, literalt b, literalt o)
{
  out << "%% limplies" << std::endl;
  out << "ASSERT (" << cvc_literal(a) << " => "
      << cvc_literal(b) << ") <=> " << cvc_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: cvc_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::land(const bvt &bv)
{
  out << "%% land" << std::endl;

  literalt literal=def_cvc_literal();

  forall_literals(it, bv)
  {
    if(it!=bv.begin()) out << " AND ";
    out << cvc_literal(*it);
  }
  
  out << ";" << std::endl << std::endl;

  return literal;  
}
  
/*******************************************************************\

Function: cvc_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lor(const bvt &bv)
{
  out << "%% lor" << std::endl;

  literalt literal=def_cvc_literal();

  forall_literals(it, bv)
  {
    if(it!=bv.begin()) out << " OR ";
    out << cvc_literal(*it);
  }
  
  out << ";" << std::endl << std::endl;

  return literal;  
}
  
/*******************************************************************\

Function: cvc_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lxor(const bvt &bv)
{
  if(bv.size()==0) return const_literal(false);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return lxor(bv[0], bv[1]);

  literalt literal=const_literal(false);

  forall_literals(it, bv)
    literal=lxor(*it, literal);

  return literal;
}
  
/*******************************************************************\

Function: cvc_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  out << "%% land" << std::endl;

  literalt o=def_cvc_literal();
  
  out << cvc_literal(a) << " AND " << cvc_literal(b) << ";"
      << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: cvc_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;
  
  out << "%% lor" << std::endl;

  literalt o=def_cvc_literal();
  
  out << cvc_literal(a) << " OR " << cvc_literal(b) << ";"
      << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: cvc_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: cvc_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  out << "%% lxor" << std::endl;

  literalt o=def_cvc_literal();
  
  out << cvc_literal(a) << " XOR " << cvc_literal(b) << ";"
      << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: cvc_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: cvc_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}

/*******************************************************************\

Function: cvc_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: cvc_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: cvc_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::lselect(literalt a, literalt b, literalt c)
{ 
  if(a==const_literal(true)) return b;
  if(a==const_literal(false)) return c;
  if(b==c) return b;

  out << "%% lselect" << std::endl;

  literalt o=def_cvc_literal();

  out << "IF " << cvc_literal(a) << " THEN "
      << cvc_literal(b) << " ELSE "
      << cvc_literal(c) << " ENDIF;"
      << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: cvc_propt::new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::new_variable()
{
  out << "l" << _no_variables << ": BOOLEAN;" << std::endl;
  literalt l;
  l.set(_no_variables, false);
  _no_variables++;
  return l;
}

/*******************************************************************\

Function: cvc_propt::def_cvc_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_propt::def_cvc_literal()
{
  out << "l" << _no_variables << ": BOOLEAN = ";
  literalt l;
  l.set(_no_variables, false);
  _no_variables++;
  return l;
}

/*******************************************************************\

Function: cvc_propt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_propt::lcnf(const bvt &bv)
{
  if(bv.empty()) return;
  bvt new_bv;

  std::set<literalt> s;

  new_bv.reserve(bv.size());

  for(bvt::const_iterator it=bv.begin(); it!=bv.end(); it++)
  {
    if(s.insert(*it).second)
      new_bv.push_back(*it);

    if(s.find(lnot(*it))!=s.end())
      return; // clause satisfied

    assert(it->var_no()<_no_variables);
  }

  assert(!new_bv.empty());

  out << "%% lcnf" << std::endl;
  out << "ASSERT ";

  for(bvt::const_iterator it=new_bv.begin(); it!=new_bv.end(); it++)
  {
    if(it!=new_bv.begin()) out << " OR ";
    out << cvc_literal(*it);
  }

  out << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: cvc_propt::cvc_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cvc_propt::cvc_literal(literalt l)
{
  if(l==const_literal(false))
    return "FALSE";
  else if(l==const_literal(true))
    return "TRUE";

  if(l.sign())
    return "(NOT l"+i2string(l.var_no())+")";  

  return "l"+i2string(l.var_no());
}

/*******************************************************************\

Function: cvc_propt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt cvc_propt::prop_solve()
{
  out << "QUERY FALSE;" << std::endl;
  return P_ERROR;
}

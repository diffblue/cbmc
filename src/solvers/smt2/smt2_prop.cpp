/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>

#include "smt2_prop.h"

/*******************************************************************\

Function: smt2_propt::smt2_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

smt2_propt::smt2_propt(
  const std::string &benchmark,
  const std::string &notes,
  const std::string &logic,
  std::ostream &_out):out(_out)
{
  out << "(benchmark " << benchmark << std::endl;
  out << ":notes \"" << notes << "\"" << std::endl;
  out << ":status unknown" << std::endl;
  out << ":logic " << logic << " ; SMT 2" << std::endl;
  _no_variables=0;
}

/*******************************************************************\

Function: smt2_propt::~smt2_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

smt2_propt::~smt2_propt()
{
}

/*******************************************************************\

Function: smt2_propt::finalize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_propt::finalize()
{
  out << std::endl;
  out << ":formula true" << std::endl;
  out << ") ; benchmark" << std::endl;
}

/*******************************************************************\

Function: smt2_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::land(const bvt &bv)
{
  out << std::endl;

  literalt l=new_variable();

  out << ":assumption ; land" << std::endl;
  out << " (= " << smt2_literal(l) << " (and";
  
  for(unsigned int i=0; i<bv.size(); i++)
    out << " " << smt2_literal(bv[i]);

  out << "))" << std::endl;

  return l;
}
  
/*******************************************************************\

Function: smt2_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lor(const bvt &bv)
{
  out << std::endl;

  literalt l=new_variable();

  out << ":assumption ; lor" << std::endl;
  out << " (= " << smt2_literal(l) << " (or";

  for(unsigned int i=0; i<bv.size(); i++)
    out << " " << smt2_literal(bv[i]);

  out << "))" << std::endl;

  return l;
}
  
/*******************************************************************\

Function: smt2_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lxor(const bvt &bv)
{
  if(bv.size()==0) return const_literal(false);
  if(bv.size()==1) return bv[0];

  out << std::endl;

  literalt l=new_variable();

  out << ":assumption ; lxor" << std::endl;
  out << " (= " << smt2_literal(l) << " (xor";

  for(unsigned int i=0; i<bv.size(); i++)
    out << " " << smt2_literal(bv[i]);

  out << "))" << std::endl;

  return l;
}
  
/*******************************************************************\

Function: smt2_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  out << std::endl;

  literalt l=new_variable();

  out << ":assumption ; land" << std::endl;
  out << " (= " << smt2_literal(l) << " (and";
  out << " " << smt2_literal(a);
  out << " " << smt2_literal(b);
  out << "))" << std::endl;

  return l;
}

/*******************************************************************\

Function: smt2_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;
  
  out << std::endl;

  literalt l=new_variable();

  out << ":assumption ; lor" << std::endl;
  out << " (= " << smt2_literal(l) << " (or";
  out << " " << smt2_literal(a);
  out << " " << smt2_literal(b);
  out << "))" << std::endl;

  return l;
}

/*******************************************************************\

Function: smt2_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: smt2_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  out << std::endl;

  literalt l=new_variable();

  out << ":assumption ; lxor" << std::endl;
  out << " (= " << smt2_literal(l) << " (xor";
  out << " " << smt2_literal(a);
  out << " " << smt2_literal(b);
  out << "))" << std::endl;

  return l;
}

/*******************************************************************\

Function: smt2_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: smt2_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}

/*******************************************************************\

Function: smt2_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: smt2_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: smt2_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::lselect(literalt a, literalt b, literalt c)
{ 
  if(a==const_literal(true)) return b;
  if(a==const_literal(false)) return c;
  if(b==c) return b;

  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  out << std::endl;

  literalt l=new_variable();

  out << ":assumption ; lselect" << std::endl;
  out << " (= " << smt2_literal(l) << "(if_then_else "
      << smt2_literal(a) << " " << smt2_literal(b) << " "
      << smt2_literal(c) << ")" << std::endl;

  return l;
}

/*******************************************************************\

Function: smt2_propt::new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_propt::new_variable()
{
  literalt l;
  l.set(_no_variables, false);
  _no_variables++;
  
  out << ":extrafuns((" << smt2_literal(l) << " Bool))" << std::endl;

  return l;
}

/*******************************************************************\

Function: smt2_propt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_propt::lcnf(const bvt &bv)
{
  out << std::endl;
  out << ":assumption ; lcnf" << std::endl;
  out << " ";

  if(bv.empty())
    out << "false ; the empty clause";
  else if(bv.size()==1)
    out << smt2_literal(bv.front());
  else
  {
    out << "(or";
    
    for(bvt::const_iterator it=bv.begin(); it!=bv.end(); it++)
      out << " " << smt2_literal(*it);

    out << ")";
  }

  out << std::endl;
}

/*******************************************************************\

Function: smt2_propt::smt2_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt2_propt::smt2_literal(literalt l)
{
  if(l==const_literal(false))
    return "false";
  else if(l==const_literal(true))
    return "true";
    
  std::string v="B"+i2string(l.var_no());

  if(l.sign())
    return "(not "+v+")";  

  return v;
}

/*******************************************************************\

Function: smt2_propt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt smt2_propt::l_get(literalt literal) const
{
  if(literal.is_true()) return tvt(true);
  if(literal.is_false()) return tvt(false);

  unsigned v=literal.var_no();
  if(v>=assignment.size()) return tvt(tvt::TV_UNKNOWN);
  tvt r=assignment[v];
  return literal.sign()?!r:r;
}

/*******************************************************************\

Function: smt2_propt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_propt::set_assignment(literalt literal, bool value)
{
  if(literal.is_true() || literal.is_false()) return;

  unsigned v=literal.var_no();
  assert(v<assignment.size());
  assignment[v]=tvt(value);
}

/*******************************************************************\

Function: smt2_propt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt smt2_propt::prop_solve()
{
  return P_ERROR;
}

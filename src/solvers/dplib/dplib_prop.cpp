/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <set>

#include <i2string.h>

#include "dplib_prop.h"

/*******************************************************************\

Function: dplib_propt::dplib_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dplib_propt::dplib_propt(std::ostream &_out):out(_out)
{
  // we skip index 0
  _no_variables=1;
}

/*******************************************************************\

Function: dplib_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::land(literalt a, literalt b, literalt o)
{
  out << "// land" << std::endl;
  out << "AXIOM (" << dplib_literal(a) << " & "
      << dplib_literal(b) << ") <=> " << dplib_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: dplib_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::lor(literalt a, literalt b, literalt o)
{
  out << "// lor" << std::endl;
  out << "AXIOM (" << dplib_literal(a) << " | "
      << dplib_literal(b) << ") <=> " << dplib_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: dplib_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::lxor(literalt a, literalt b, literalt o)
{
  out << "// lxor" << std::endl;
  out << "AXIOM (" << dplib_literal(a) << " <=> "
      << dplib_literal(b) << ") <=> !" << dplib_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: dplib_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::lnand(literalt a, literalt b, literalt o)
{
  out << "// lnand" << std::endl;
  out << "AXIOM (" << dplib_literal(a) << " & "
      << dplib_literal(b) << ") <=> !" << dplib_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: dplib_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::lnor(literalt a, literalt b, literalt o)
{
  out << "// lnor" << std::endl;
  out << "AXIOM (" << dplib_literal(a) << " | "
      << dplib_literal(b) << ") <=> !" << dplib_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: dplib_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::lequal(literalt a, literalt b, literalt o)
{
  out << "// lequal" << std::endl;
  out << "AXIOM (" << dplib_literal(a) << " <=> "
      << dplib_literal(b) << ") <=> " << dplib_literal(o)
      << ";" << std::endl << std::endl;
}
  
/*******************************************************************\

Function: dplib_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::limplies(literalt a, literalt b, literalt o)
{
  out << "// limplies" << std::endl;
  out << "AXIOM (" << dplib_literal(a) << " => "
      << dplib_literal(b) << ") <=> " << dplib_literal(o)
      << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: dplib_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::land(const bvt &bv)
{
  out << "// land" << std::endl;

  literalt literal=def_dplib_literal();

  forall_literals(it, bv)
  {
    if(it!=bv.begin()) out << " & ";
    out << dplib_literal(*it);
  }
  
  out << std::endl << std::endl;

  return literal;  
}
  
/*******************************************************************\

Function: dplib_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lor(const bvt &bv)
{
  out << "// lor" << std::endl;

  literalt literal=def_dplib_literal();

  forall_literals(it, bv)
  {
    if(it!=bv.begin()) out << " | ";
    out << dplib_literal(*it);
  }
  
  out << std::endl << std::endl;

  return literal;  
}
  
/*******************************************************************\

Function: dplib_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lxor(const bvt &bv)
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

Function: dplib_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  literalt o=def_dplib_literal();
  out << dplib_literal(a) << " & " << dplib_literal(b)
      << ";" << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: dplib_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;
  
  literalt o=def_dplib_literal();
  out << dplib_literal(a) << " | " << dplib_literal(b)
      << ";" << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: dplib_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: dplib_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  literalt o=def_dplib_literal();
  out << "!(" << dplib_literal(a) << " <-> " << dplib_literal(b)
      << ");" << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: dplib_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: dplib_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}

/*******************************************************************\

Function: dplib_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: dplib_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: dplib_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::lselect(literalt a, literalt b, literalt c)
{ 
  if(a==const_literal(true)) return b;
  if(a==const_literal(false)) return c;
  if(b==c) return b;

  out << "// lselect" << std::endl;

  literalt o=def_dplib_literal();

  out << "IF " << dplib_literal(a) << " THEN "
      << dplib_literal(b) << " ELSE "
      << dplib_literal(c) << " ENDIF;"
      << std::endl << std::endl;

  return o;
}

/*******************************************************************\

Function: dplib_propt::new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::new_variable()
{
  _no_variables++;
  out << "l" << _no_variables << ": boolean;" << std::endl;
  literalt l;
  l.set(_no_variables, false);
  return l;
}

/*******************************************************************\

Function: dplib_propt::def_dplib_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt dplib_propt::def_dplib_literal()
{
  _no_variables++;
  out << "l" << _no_variables << ": boolean = ";
  literalt l;
  l.set(_no_variables, false);
  return l;
}

/*******************************************************************\

Function: dplib_propt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::lcnf(const bvt &bv)
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

    assert(it->var_no()<=_no_variables);
  }

  assert(!new_bv.empty());

  out << "// lcnf" << std::endl;
  out << "AXIOM ";

  for(bvt::const_iterator it=new_bv.begin(); it!=new_bv.end(); it++)
  {
    if(it!=new_bv.begin()) out << " | ";
    out << dplib_literal(*it);
  }

  out << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: dplib_propt::dplib_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string dplib_propt::dplib_literal(literalt l)
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

Function: dplib_propt::finish

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dplib_propt::finish()
{
  // we want satisfiability
  out << "THEOREM false;" << std::endl;
}

/*******************************************************************\

Function: dplib_propt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt dplib_propt::prop_solve()
{
  finish();
  return P_ERROR;
}

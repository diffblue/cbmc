/*******************************************************************\

Module: CNF Generation, via Tseitin

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>
#include <set>

#include "cnf.h"
//#define VERBOSE

/*******************************************************************\

Function: cnft::cnft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cnft::cnft()
{
  // for CNF, we don't use 0 as a matter of principle
  _no_variables=1;
}

/*******************************************************************\

Function: cnft::~cnft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cnft::~cnft()
{
}

/*******************************************************************\

Function: cnft::gate_and

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_and(literalt a, literalt b, literalt o)
{
  // a*b=c <==> (a + o')( b + o')(a'+b'+o)
  bvt lits;

  lits.clear();
  lits.reserve(2);
  lits.push_back(pos(a));
  lits.push_back(neg(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(2);
  lits.push_back(pos(b));
  lits.push_back(neg(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(neg(a));
  lits.push_back(neg(b));
  lits.push_back(pos(o));
  lcnf(lits);
}

/*******************************************************************\

Function: cnft::gate_or

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_or(literalt a, literalt b, literalt o)
{
  // a+b=c <==> (a' + c)( b' + c)(a + b + c')
  bvt lits;

  lits.clear();
  lits.reserve(2);
  lits.push_back(neg(a));
  lits.push_back(pos(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(2);
  lits.push_back(neg(b));
  lits.push_back(pos(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(pos(a));
  lits.push_back(pos(b));
  lits.push_back(neg(o));
  lcnf(lits);
}

/*******************************************************************\

Function: cnft::gate_xor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_xor(literalt a, literalt b, literalt o)
{
  // a xor b = o <==> (a' + b' + o')
  //                  (a + b + o' )
  //                  (a' + b + o)
  //                  (a + b' + o)
  bvt lits;

  lits.clear();
  lits.reserve(3);
  lits.push_back(neg(a));
  lits.push_back(neg(b));
  lits.push_back(neg(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(pos(a));
  lits.push_back(pos(b));
  lits.push_back(neg(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(neg(a));
  lits.push_back(pos(b));
  lits.push_back(pos(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(pos(a));
  lits.push_back(neg(b));
  lits.push_back(pos(o));
  lcnf(lits);
}

/*******************************************************************\

Function: cnft::gate_nand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_nand(literalt a, literalt b, literalt o)
{
  // a Nand b = o <==> (a + o)( b + o)(a' + b' + o')
  bvt lits;

  lits.clear();
  lits.reserve(2);
  lits.push_back(pos(a));
  lits.push_back(pos(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(2);
  lits.push_back(pos(b));
  lits.push_back(pos(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(neg(a));
  lits.push_back(neg(b));
  lits.push_back(neg(o));
  lcnf(lits);
}

/*******************************************************************\

Function: cnft::gate_nor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_nor(literalt a, literalt b, literalt o)
{
  // a Nor b = o <==> (a' + o')( b' + o')(a + b + o)
  bvt lits;

  lits.clear();
  lits.reserve(2);
  lits.push_back(neg(a));
  lits.push_back(neg(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(2);
  lits.push_back(neg(b));
  lits.push_back(neg(o));
  lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(pos(a));
  lits.push_back(pos(b));
  lits.push_back(pos(o));
  lcnf(lits);
}

/*******************************************************************\

Function: cnft::gate_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_equal(literalt a, literalt b, literalt o)
{
  gate_xor(a, b, lnot(o));
}
  
/*******************************************************************\

Function: cnft::gate_implies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_implies(literalt a, literalt b, literalt o)
{
  gate_or(lnot(a), b, o);
}

/*******************************************************************\

Function: cnft::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::land(const bvt &bv)
{
  if(bv.size()==0) return const_literal(true);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return land(bv[0], bv[1]);

  forall_literals(it, bv)
    if(*it==const_literal(false))
      return const_literal(false);

  if(is_all(bv, const_literal(true)))
    return const_literal(true);

  bvt new_bv;

  eliminate_duplicates(bv, new_bv);

  literalt literal=new_variable();

  forall_literals(it, new_bv)
  {
    bvt lits;
    lits.reserve(2);
    lits.push_back(pos(*it));
    lits.push_back(neg(literal));
    lcnf(lits);
  }

  bvt lits;
  lits.reserve(new_bv.size()+1);

  forall_literals(it, new_bv)
    lits.push_back(neg(*it));

  lits.push_back(pos(literal));
  lcnf(lits);

  return literal;  
}
  
/*******************************************************************\

Function: cnft::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lor(const bvt &bv)
{
  if(bv.size()==0) return const_literal(false);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return lor(bv[0], bv[1]);

  forall_literals(it, bv)
    if(*it==const_literal(true))
      return const_literal(true);

  if(is_all(bv, const_literal(false)))
    return const_literal(false);

  bvt new_bv;

  eliminate_duplicates(bv, new_bv);

  literalt literal=new_variable();

  forall_literals(it, new_bv)
  {
    bvt lits;
    lits.reserve(2);
    lits.push_back(neg(*it));
    lits.push_back(pos(literal));
    lcnf(lits);
  }

  bvt lits;
  lits.reserve(new_bv.size()+1);

  forall_literals(it, new_bv)
    lits.push_back(pos(*it));

  lits.push_back(neg(literal));
  lcnf(lits);

  return literal;
}
  
/*******************************************************************\

Function: cnft::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lxor(const bvt &bv)
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

Function: cnft::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  literalt o=new_variable();
  gate_and(a, b, o);
  return o;
}

/*******************************************************************\

Function: cnft::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;

  literalt o=new_variable();
  gate_or(a, b, o);
  return o;
}

/*******************************************************************\

Function: cnft::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: cnft::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  literalt o=new_variable();
  gate_xor(a, b, o);
  return o;
}

/*******************************************************************\

Function: cnft::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: cnft::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}

/*******************************************************************\

Function: cnft::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: cnft::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: cnft::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lselect(literalt a, literalt b, literalt c)
{  // a?b:c = (a AND b) OR (/a AND c)
  if(a==const_literal(true)) return b;
  if(a==const_literal(false)) return c;
  if(b==c) return b;

  bvt bv;
  bv.reserve(2);
  bv.push_back(land(a, b));
  bv.push_back(land(lnot(a), c));
  return lor(bv);
}

/*******************************************************************\

Function: cnft::new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::new_variable()
{
  literalt l;
  l.set(_no_variables, false);

  set_no_variables(_no_variables+1);

  return l;
}

/*******************************************************************\

Function: cnft::eliminate_duplicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::eliminate_duplicates(const bvt &bv, bvt &dest)
{
  std::set<literalt> s;

  dest.reserve(bv.size());

  for(bvt::const_iterator it=bv.begin(); it!=bv.end(); it++)
  {
    if(s.insert(*it).second)
      dest.push_back(*it);
  }
}

/*******************************************************************\

Function: cnft::process_clause

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cnft::process_clause(const bvt &bv, bvt &dest)
{
  dest.clear();

  // empty clause! this is UNSAT
  if(bv.empty()) return false;

  std::set<literalt> s;

  dest.reserve(bv.size());

  for(bvt::const_iterator it=bv.begin();
      it!=bv.end();
      it++)
  {
    literalt l=*it;
    
    // we never use index 0
    assert(l.var_no()!=0);
    
    // we never use 'unused_var_no'
    assert(l.var_no()!=literalt::unused_var_no());

    if(l.is_true())
      return true; // clause satisfied

    if(l.is_false())
      continue;

    if(l.var_no()>=_no_variables)
      std::cout << "l.var_no()=" << l.var_no() << " _no_variables=" << _no_variables << std::endl;
    assert(l.var_no()<_no_variables);

    // prevent duplicate literals
    if(s.insert(l).second)
      dest.push_back(l);

    if(s.find(lnot(l))!=s.end())
      return true; // clause satisfied
  }
  
  return false;
}

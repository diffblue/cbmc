/*******************************************************************\

Module: CNF Generation, via Tseitin

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
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

cnft::cnft() :
  _no_variables(1) // for CNF, we don't use 0 as a matter of principle
{
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
  bvt lits(2);

  lits[0]=pos(a);
  lits[1]=neg(o);
  lcnf(lits);

  lits[0]=pos(b);
  lits[1]=neg(o);
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
  bvt lits(2);

  lits[0]=neg(a);
  lits[1]=pos(o);
  lcnf(lits);

  lits[0]=neg(b);
  lits[1]=pos(o);
  lcnf(lits);

  lits.resize(3);
  lits[0]=pos(a);
  lits[1]=pos(b);
  lits[2]=neg(o);
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
  bvt lits(3);

  lits[0]=neg(a);
  lits[1]=neg(b);
  lits[2]=neg(o);
  lcnf(lits);

  lits[0]=pos(a);
  lits[1]=pos(b);
  lits[2]=neg(o);
  lcnf(lits);

  lits[0]=neg(a);
  lits[1]=pos(b);
  lits[2]=pos(o);
  lcnf(lits);

  lits[0]=pos(a);
  lits[1]=neg(b);
  lits[2]=pos(o);
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
  bvt lits(2);

  lits[0]=pos(a);
  lits[1]=pos(o);
  lcnf(lits);

  lits[0]=pos(b);
  lits[1]=pos(o);
  lcnf(lits);

  lits.resize(3);
  lits[0]=neg(a);
  lits[1]=neg(b);
  lits[2]=neg(o);
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
  bvt lits(2);

  lits[0]=neg(a);
  lits[1]=neg(o);
  lcnf(lits);

  lits[0]=neg(b);
  lits[1]=neg(o);
  lcnf(lits);

  lits.resize(3);
  lits[0]=pos(a);
  lits[1]=pos(b);
  lits[2]=pos(o);
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
  gate_xor(a, b, !o);
}
  
/*******************************************************************\

Function: cnft::gate_implies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnft::gate_implies(literalt a, literalt b, literalt o)
{
  gate_or(!a, b, o);
}

/*******************************************************************\

Function: cnft::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::land(const bvt &bv)
{
  if(bv.empty()) return const_literal(true);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return land(bv[0], bv[1]);

  forall_literals(it, bv)
    if(it->is_false())
      return *it;

  if(is_all(bv, const_literal(true)))
    return const_literal(true);

  bvt new_bv;

  eliminate_duplicates(bv, new_bv);

  bvt lits(2);
  literalt literal=new_variable();
  lits[1]=neg(literal);

  forall_literals(it, new_bv)
  {
    lits[0]=pos(*it);
    lcnf(lits);
  }

  lits.clear();
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
  if(bv.empty()) return const_literal(false);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return lor(bv[0], bv[1]);

  forall_literals(it, bv)
    if(it->is_true())
      return *it;

  if(is_all(bv, const_literal(false)))
    return const_literal(false);

  bvt new_bv;

  eliminate_duplicates(bv, new_bv);

  bvt lits(2);
  literalt literal=new_variable();
  lits[1]=pos(literal);

  forall_literals(it, new_bv)
  {
    lits[0]=neg(*it);
    lcnf(lits);
  }

  lits.clear();
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
  if(bv.empty()) return const_literal(false);
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
  if(a.is_true()) return b;
  if(b.is_true()) return a;
  if(a.is_false()) return a;
  if(b.is_false()) return b;
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
  if(a.is_false()) return b;
  if(b.is_false()) return a;
  if(a.is_true()) return a;
  if(b.is_true()) return b;
  if(a==b) return a;

  literalt o=new_variable();
  gate_or(a, b, o);
  return o;
}

/*******************************************************************\

Function: cnft::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lxor(literalt a, literalt b)
{
  if(a.is_false()) return b;
  if(b.is_false()) return a;
  if(a.is_true()) return !b;
  if(b.is_true()) return !a;
  if(a==b) return const_literal(false);
  if(a==!b) return const_literal(true);

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
  return !land(a, b);
}

/*******************************************************************\

Function: cnft::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lnor(literalt a, literalt b)
{
  return !lor(a, b);
}

/*******************************************************************\

Function: cnft::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::lequal(literalt a, literalt b)
{
  return !lxor(a, b);
}

/*******************************************************************\

Function: cnft::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cnft::limplies(literalt a, literalt b)
{
  return lor(!a, b);
}

/*******************************************************************\

Function: cnft::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// Tino observed slow-downs up to 50% with OPTIMAL_COMPACT_ITE.

#define COMPACT_ITE
//#define OPTIMAL_COMPACT_ITE

literalt cnft::lselect(literalt a, literalt b, literalt c)
{ // a?b:c = (a AND b) OR (/a AND c)

  if(a.is_constant()) return a.sign() ? b : c;
  if(b==c) return b;

  if(b.is_constant()) return b.sign() ? lor(a, c) : land(!a, c);
  if(c.is_constant()) return c.sign() ? lor(!a, b) : land(a, b);

  #ifdef COMPACT_ITE

  // (a+c'+o) (a+c+o') (a'+b'+o) (a'+b+o')

  literalt o=new_variable();

  bvt lits;
  
  lcnf( a, !c,  o);
  lcnf( a,  c, !o);
  lcnf(!a, !b,  o);
  lcnf(!a,  b, !o);

  #ifdef OPTIMAL_COMPACT_ITE
  // additional clauses to enable better propagation
  lcnf( b,  c, !o);
  lcnf(!b, !c,  o);
  #endif

  return o;

  #else
  return lor(land(a, b), land(!a, c));
  #endif
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

  forall_literals(it, bv)
    if(s.insert(*it).second)
      dest.push_back(*it);
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

  // first check simple things
  
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
      continue; // will remove later

    if(l.var_no()>=_no_variables)
      std::cout << "l.var_no()=" << l.var_no() << " _no_variables=" << _no_variables << std::endl;

    assert(l.var_no()<_no_variables);
  }
  
  // now copy
  dest.clear();
  dest.reserve(bv.size());
  
  for(bvt::const_iterator it=bv.begin();
      it!=bv.end();
      it++)
  {
    literalt l=*it;
    
    if(l.is_false())
      continue; // remove

    dest.push_back(l);
  }
  
  // now sort
  std::sort(dest.begin(), dest.end());

  // eliminate duplicates and find occurrences of a variable
  // and its negation
  
  if(dest.size()>=2)
  {
    bvt::iterator it=dest.begin();
    literalt previous=*it;
  
    for(it++;
        it!=dest.end();
        ) // no it++
    {
      literalt l=*it;
      
      // prevent duplicate literals
      if(l==previous)
        it=dest.erase(it);
      else if(previous==!l)
        return true; // clause satisfied trivially
      else
      {
        previous=l;
        it++;
      }
    }
  }
  
  return false;
}

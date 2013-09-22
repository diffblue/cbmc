/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>
#include <stack>

#include "aig_prop.h"

/*******************************************************************\

Function: aig_prop_baset::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::land(const bvt &bv)
{
  literalt literal=const_literal(true);

  forall_literals(it, bv)
    literal=land(*it, literal);

  return literal;
}
  
/*******************************************************************\

Function: aig_prop_baset::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lor(const bvt &bv)
{
  literalt literal=const_literal(false);

  forall_literals(it, bv)
    literal=lor(*it, literal);

  return literal;
}
  
/*******************************************************************\

Function: aig_prop_baset::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lxor(const bvt &bv)
{
  literalt literal=const_literal(false);

  forall_literals(it, bv)
    literal=lxor(*it, literal);

  return literal;
}
  
/*******************************************************************\

Function: aig_prop_baset::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::land(literalt a, literalt b)
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

Function: aig_prop_baset::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lor(literalt a, literalt b)
{
  return neg(land(neg(a), neg(b))); // De Morgan's
}

/*******************************************************************\

Function: aig_prop_baset::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lnot(literalt a)
{
  return neg(a);
}

/*******************************************************************\

Function: aig_prop_baset::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lxor(literalt a, literalt b)
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

Function: aig_prop_baset::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lnand(literalt a, literalt b)
{
  return !land(a, b);
}

/*******************************************************************\

Function: aig_prop_baset::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lnor(literalt a, literalt b)
{
  return !lor(a, b);
}

/*******************************************************************\

Function: aig_prop_baset::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lequal(literalt a, literalt b)
{
  return !lxor(a, b);
}

/*******************************************************************\

Function: aig_prop_baset::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::limplies(literalt a, literalt b)
{
  return lor(neg(a), b);
}

/*******************************************************************\

Function: aig_prop_baset::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::lselect(literalt a, literalt b, literalt c)
{  // a?b:c = (a AND b) OR (/a AND c)
  if(a.is_true()) return b;
  if(a.is_false()) return c;
  if(b==c) return b;

  return lor(land(a, b), land(neg(a), c));
}

/*******************************************************************\

Function: aig_prop_constraintt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aig_prop_constraintt::lcnf(const bvt &clause)
{
  l_set_to_true(lor(clause));
}
  
/*******************************************************************\

Function: aig_prop_baset::set_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aig_prop_baset::set_equal(literalt a, literalt b)
{
  // we produce two constraints:
  // a|!b   !a|b

  l_set_to_true(lor(pos(a), neg(b)));
  l_set_to_true(lor(neg(a), pos(b)));
}

/*******************************************************************\

Function: aig_prop_solvert::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt aig_prop_solvert::l_get(literalt a) const
{
  return solver.l_get(a);
}

/*******************************************************************\

Function: aig_prop_solvert::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt aig_prop_solvert::prop_solve()
{
  status() << "converting AIG, "
           << aig.nodes.size() << " nodes" << eom;
  convert_aig();

  return solver.prop_solve();
}

/*******************************************************************\

Function: aig_prop_solvert::convert_aig

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aig_prop_solvert::convert_aig()
{
  // 1. Do variables
  
  while(solver.no_variables()<=aig.nodes.size())
    solver.new_variable();

  #if 0
  // Get phases
  std::vector<bool> n_pos, n_neg;
  n_pos.resize(aig.nodes.size(), false);
  n_neg.resize(aig.nodes.size(), false);

  std::stack<literalt> queue;

  // Get phases of constraints
  for(constraintst::const_iterator
      c_it=constraints.begin();
      c_it!=constraints.end();
      c_it++)
    queue.push(*c_it);

  while(!queue.empty())
  {
    literalt l=queue.top();
    queue.pop();

    if(l.is_constant()) continue;

    bool sign=l.sign();
    unsigned var_no=l.var_no();
    
    // already set?
    if(sign?n_neg[var_no]:n_pos[var_no]) continue; // done already
    
    // set
    sign?n_neg[var_no]=1:n_pos[var_no]=1;
    
    const aigt::nodet &node=aig.nodes[var_no];

    if(node.is_and())
    {
      queue.push(node.a^sign);
      queue.push(node.b^sign);
    }    
  }  
  
  // Count
  unsigned pos_only=0, neg_only=0, mixed=0;
  
  for(unsigned n=0; n<aig.nodes.size(); n++)
  {
    if(aig.nodes[n].is_and())
    {
      if(n_neg[n] && n_pos[n])
        mixed++;
      else if(n_pos[n])
        pos_only++;
      else if(n_neg[n])
        neg_only++;
    }
  }
  
  statistics() << "Pos only: " << pos_only << "\n"
               << "Neg only: " << neg_only << "\n"
               << "Mixed: " << mixed << eom;

  for(unsigned n=0; n<aig.nodes.size(); n++)
  {
    const aigt::nodet &node=aig.nodes[n];

    if(node.is_and())
    {
      literalt o=literalt(n, false);
      literalt a=node.a;
      literalt b=node.b;
      
      if(n_pos[n])
      {
        bvt lits(2);

        lits[0]=pos(a);
        lits[1]=neg(o);
        solver.lcnf(lits);

        lits[0]=pos(b);
        lits[1]=neg(o);
        solver.lcnf(lits);
      }

      if(n_neg[n])
      {
        bvt lits(3);
        lits[0]=neg(a);
        lits[1]=neg(b);
        lits[2]=pos(o);
        solver.lcnf(lits);
      }
    }
  }

  #else
            
  // 2. Do nodes

  for(unsigned n=0; n<aig.nodes.size(); n++)
  {
    const aigt::nodet &node=aig.nodes[n];

    if(node.is_and())
    {
      literalt o=literalt(n, false);
      literalt a=node.a;
      literalt b=node.b;
      
      bvt lits(2);
   
      lits[0]=pos(a);
      lits[1]=neg(o);
      solver.lcnf(lits);

      lits[0]=pos(b);
      lits[1]=neg(o);
      solver.lcnf(lits);

      lits.clear();
      lits.reserve(3);
      lits.push_back(neg(a));
      lits.push_back(neg(b));
      lits.push_back(pos(o));
      solver.lcnf(lits);
    }
  }
  #endif
  
  // 3. Do constraints
  
  for(constraintst::const_iterator
      c_it=constraints.begin();
      c_it!=constraints.end();
      c_it++)
  {
    solver.l_set_to(*c_it, true);
  }
}

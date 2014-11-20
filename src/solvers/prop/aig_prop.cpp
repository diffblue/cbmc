/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>
#include <stack>

#include "aig_prop.h"

#define USE_AIG_COMPACT
#define USE_PG

/*******************************************************************\

Function: aig_prop_baset::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_prop_baset::land(const bvt &bv)
{
  literalt literal=const_literal(true);

  // Introduces N-1 extra nodes for N bits
  // See convert_node for where this overhead is removed
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
  literalt literal=const_literal(true);

  // Introduces N-1 extra nodes for N bits
  // See convert_node for where this overhead is removed
  forall_literals(it, bv)
    literal=land(neg(*it), literal);

  return neg(literal);
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
  // See convert_node for where this overhead is removed
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

  // This produces unnecessary clauses and variables
  // See convert_node for where this overhead is removed

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
#ifdef USE_AIG_COMPACT
  // The compact encoding should reduce this
  l_set_to_true(lequal(a,b));

#else
  // we produce two constraints:
  // a|!b   !a|b

  l_set_to_true(lor(pos(a), neg(b)));
  l_set_to_true(lor(neg(a), pos(b)));
#endif
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

Function: aig_prop_solvert::compute_phase

  Inputs: Two vectors of bools of size aig.nodes.size()

 Outputs: These vectors filled in with per node phase information

 Purpose: Compute the phase information needed for Plaisted-Greenbaum encoding

\*******************************************************************/

void aig_prop_solvert::compute_phase(std::vector<bool> &n_pos, std::vector<bool> &n_neg) {
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
}


/*******************************************************************\

Function: aig_prop_solvert::usage_count

  Inputs: Two vectors of unsigned of size aig.nodes.size()

 Outputs: These vectors filled in with per node usage information

 Purpose: Compact encoding for single usage variable

\*******************************************************************/

void aig_prop_solvert::usage_count(std::vector<unsigned> &p_usage_count, std::vector<unsigned> &n_usage_count) {

  for (constraintst::const_iterator
      c_it=constraints.begin();
      c_it!=constraints.end();
       c_it++) {
    if (!((*c_it).is_constant())) {

      if ((*c_it).sign()) {
	++n_usage_count[(*c_it).var_no()];
      } else {
	++p_usage_count[(*c_it).var_no()];
      }

    }
  }

  for (unsigned n=0; n<aig.nodes.size(); n++) {
    const aigt::nodet &node=aig.nodes[n];

    if (node.is_and()) {
      if (node.a.sign()) {
	++n_usage_count[node.a.var_no()];
      } else {
	++p_usage_count[node.a.var_no()];
      }

      if (node.b.sign()) {
	++n_usage_count[node.b.var_no()];
      } else {
	++p_usage_count[node.b.var_no()];
      }

    }
  }


  #if 1
  // Compute stats
  unsigned unused = 0;
  unsigned usedOncePositive = 0;
  unsigned usedOnceNegative = 0;
  unsigned usedTwicePositive = 0;
  unsigned usedTwiceNegative = 0;
  unsigned usedTwiceMixed = 0;
  unsigned usedThreeTimes = 0;
  unsigned usedMore = 0;

  for (unsigned n=0; n<aig.nodes.size(); n++) {
    switch (p_usage_count[n] + n_usage_count[n]) {
    case 0 : ++unused; break;
    case 1 :
      if (p_usage_count[n] == 1) {
	++usedOncePositive;
      } else {
	++usedOnceNegative;
      }
      break;

    case 2 :
      if (p_usage_count[n] >= 2) {
	++usedTwicePositive;

      } else if (n_usage_count[n] >= 2) {
	++usedTwiceNegative;

      } else {
	assert(p_usage_count[n] == 1 && n_usage_count[n] == 1);
	++usedTwiceMixed;

      }
      break;
    case 3 : ++usedThreeTimes; break;
    default : ++usedMore; break;
    }
  }

  statistics() << "Unused: " << unused << " "
	       << "Used once: " << usedOncePositive + usedOnceNegative
	       << " (P: " << usedOncePositive
               << ", N: " << usedOnceNegative << ") "
	       << "Used twice: " << usedTwicePositive + usedTwiceNegative + usedTwiceMixed
               << " (P: " << usedTwicePositive
               << ", N: " << usedTwiceNegative
               << ", M: " << usedTwiceMixed << ") "
	       << "Used three times: " << usedThreeTimes << " "
	       << "Used more: " << usedMore
	       << eom;
  #endif
}


/*******************************************************************\

Function: aig_prop_solvert::convert_node

  Inputs: The node to convert, the phases required and the usage counts.

 Outputs: The node converted to CNF in the solver object.

 Purpose: Convert one AIG node, including special handling of a couple of cases

\*******************************************************************/

void aig_prop_solvert::convert_node(
  unsigned n,
  const aigt::nodet &node,
  bool n_pos, bool n_neg,
  std::vector<unsigned> &p_usage_count,
  std::vector<unsigned> &n_usage_count)
{

  if (p_usage_count[n] > 0 || n_usage_count[n] > 0) {
    
    literalt o=literalt(n, false);
    bvt body(2);
    body[0]=node.a;
    body[1]=node.b;

#ifdef USE_AIG_COMPACT
    // Inline positive literals
    // This should remove the overhead introduced by land and lor for bvt
    
    for (bvt::size_type i = 0; i < body.size(); i++) {
      literalt l = body[i];
      
      if (!l.sign() &&                      // Used positively...
	  aig.nodes[l.var_no()].is_and() && // ... is a gate ...
	  p_usage_count[l.var_no()] == 1 && // ... only used here.
	  n_usage_count[l.var_no()] == 0) {
	
	const aigt::nodet &rep = aig.nodes[l.var_no()];
	body[i] = rep.a;
	body.push_back(rep.b);
	--i;                         // Repeat the process
	--p_usage_count[l.var_no()]; // Supress generation of inlined node
      }
    }

    // TODO : Could check the array for duplicates / complementary literals
    // but this should be found by the SAT preprocessor.
    // TODO : Likewise could find things that are constrained, esp the output
    // and backwards constant propagate.  Again may not be worth it.



    // lxor and lselect et al. are difficult to express in AIGs.
    // Doing so introduces quite a bit of overhead.
    // This should recognise the AIGs they produce and
    // handle them in a more efficient way.
    
    // Recognise something of the form:
    //
    //  neg(o) = lor(land(a,b), land(neg(a),c))
    //      o  = land(lneg(land(a,b)), lneg(land(neg(a),c)))
    // 
    // Note that lxor and lselect generate the negation of this
    // but will still be recognised because the negation is
    // recorded where it is used
    
    if (body.size() == 2 && body[0].sign() && body[1].sign()) {

      const aigt::nodet &left = aig.nodes[body[0].var_no()];
      const aigt::nodet &right = aig.nodes[body[1].var_no()];
      
      if(left.is_and() && right.is_and())
      {
	if(left.a == neg(right.a))
	{
	  if (p_usage_count[body[0].var_no()] == 0 &&
	      n_usage_count[body[0].var_no()] == 1 &&
	      p_usage_count[body[1].var_no()] == 0 &&
	      n_usage_count[body[1].var_no()] == 1)
          {
	    bvt lits(3);

	    if (n_neg)
	    {
	      lits[0] = left.a;
	      lits[1] = right.b;
	      lits[2] = o;
	      solver.lcnf(lits);
	      
	      lits[0] = neg(left.a);
	      lits[1] = left.b;
	      lits[2] = o;
	      solver.lcnf(lits);
	    }

	    if (n_pos)
	    {
	      lits[0] = left.a;
	      lits[1] = neg(right.b);
	      lits[2] = neg(o);
	      solver.lcnf(lits);
	      
	      lits[0] = neg(left.a);
	      lits[1] = neg(left.b);
	      lits[2] = neg(o);
	      solver.lcnf(lits);
	    }

	    // Supress generation
	    --n_usage_count[body[0].var_no()];
	    --n_usage_count[body[1].var_no()];
	    
	    return;
	  }
	}
      }      
    }


    // Likewise, carry has an improved encoding which is generated
    // by the CNF encoding
    if (body.size() == 3 && body[0].sign() && body[1].sign() && body[2].sign()) {
      const aigt::nodet &left = aig.nodes[body[0].var_no()];
      const aigt::nodet &mid = aig.nodes[body[1].var_no()];
      const aigt::nodet &right = aig.nodes[body[2].var_no()];

      if (left.is_and() && mid.is_and() && right.is_and()) {
	if (p_usage_count[body[0].var_no()] == 0 &&
	    n_usage_count[body[0].var_no()] == 1 &&
	    p_usage_count[body[1].var_no()] == 0 &&
	    n_usage_count[body[1].var_no()] == 1 &&
	    p_usage_count[body[2].var_no()] == 0 &&
	    n_usage_count[body[2].var_no()] == 1) {

	  literalt a = left.a;
	  literalt b = left.b;
	  literalt c = mid.a;

	  if (a == right.b && b == mid.b && c == right.a) {

	    // A (negative) carry -- 1 if at most one input is 1
	    bvt lits(3);

	    if (n_neg)
	    {
	      lits[0] = a;
	      lits[1] = b;
	      lits[2] = o;
	      solver.lcnf(lits);

	      lits[0] = a;
	      lits[1] = c;
	      lits[2] = o;
	      solver.lcnf(lits);
	      
	      lits[0] = b;
	      lits[1] = c;
	      lits[2] = o;
	      solver.lcnf(lits);
	    }

	    if (n_pos)
	    {
	      lits[0] = neg(a);
	      lits[1] = neg(b);
	      lits[2] = neg(o);
	      solver.lcnf(lits);

	      lits[0] = neg(a);
	      lits[1] = neg(c);
	      lits[2] = neg(o);
	      solver.lcnf(lits);
	      
	      lits[0] = neg(b);
	      lits[1] = neg(c);
	      lits[2] = neg(o);
	      solver.lcnf(lits);
	    }

	    // Supress generation
	    --n_usage_count[body[0].var_no()];
	    --n_usage_count[body[1].var_no()];
	    --n_usage_count[body[2].var_no()];
	    
	    return;
	  }
	}
      }
    }

    // TODO : these special cases are fragile and could be improved.
    // They don't handle cases where the construction is partially constant
    // folded.  Also the usage constraints are sufficient for improvement
    // but reductions may still be possible with looser restrictions.


#endif

    if(n_pos)
      {
	bvt lits(2);
	lits[1]=neg(o);
	
	forall_literals(it, body)
	{
	  lits[0]=pos(*it);
	  solver.lcnf(lits);
	}
      }
    
    if(n_neg)
      {
	bvt lits;
	
	forall_literals(it, body)
	  lits.push_back(neg(*it));

	lits.push_back(pos(o));
	solver.lcnf(lits);
      }

  }
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

  // Usage count for inlining

  std::vector<unsigned> p_usage_count;
  std::vector<unsigned> n_usage_count;
  p_usage_count.resize(aig.nodes.size(), 0);
  n_usage_count.resize(aig.nodes.size(), 0);

  this->usage_count(p_usage_count, n_usage_count);


  #ifdef USE_PG
  // Get phases
  std::vector<bool> n_pos, n_neg;
  n_pos.resize(aig.nodes.size(), false);
  n_neg.resize(aig.nodes.size(), false);

  this->compute_phase(n_pos, n_neg);
  #endif


  // 2. Do nodes
  for(unsigned n = aig.nodes.size() - 1; n != 0; n--)
  {
    if(aig.nodes[n].is_and())
      {
#ifdef USE_PG
	convert_node(n, aig.nodes[n], n_pos[n], n_neg[n], p_usage_count, n_usage_count);
#else
	convert_node(n, aig.nodes[n], true, true, p_usage_count, n_usage_count);
#endif
      }
  }
  // Skip zero as it is not used or a valid literal

  
  // 3. Do constraints
  for(constraintst::const_iterator
      c_it=constraints.begin();
      c_it!=constraints.end();
      c_it++)
  {
    solver.l_set_to(*c_it, true);
  }

  // HACK!
  aig.nodes.clear();

}

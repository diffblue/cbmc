/*******************************************************************\

Module: CNF Generation, via Tseitin

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CNF Generation, via Tseitin

#include "cnf.h"

#include <algorithm>
#include <set>

#include <util/invariant.h>

// #define VERBOSE

/// Tseitin encoding of conjunction of two literals. Side effect: add clauses
/// that encodes relation between inputs/output via lcnf.
/// \par parameters: Two input signals to the AND gate, one output
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

/// Tseitin encoding of disjunction of two literals
/// \par parameters: Two input signals to the OR gate, one output
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

/// Tseitin encoding of XOR of two literals
/// \par parameters: Two input signals to the XOR gate, one output
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

/// Tseitin encoding of NAND of two literals
/// \par parameters: Two input signals to the NAND gate, one output
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

/// Tseitin encoding of NOR of two literals
/// \par parameters: Two input signals to the NOR gate, one output
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

/// Tseitin encoding of equality between two literals
/// \par parameters: Two input signals to the EQUAL gate, one output
void cnft::gate_equal(literalt a, literalt b, literalt o)
{
  gate_xor(a, b, !o);
}

/// Tseitin encoding of implication between two literals
/// \par parameters: Two input signals to the IMPLIES gate, one output
void cnft::gate_implies(literalt a, literalt b, literalt o)
{
  gate_or(!a, b, o);
}

/// Tseitin encoding of conjunction between multiple literals
/// \par parameters: Any number of inputs to the AND gate
/// \return Output signal of the AND gate as literal
literalt cnft::land(const bvt &bv)
{
  if(bv.empty())
    return const_literal(true);
  if(bv.size()==1)
    return bv[0];
  if(bv.size()==2)
    return land(bv[0], bv[1]);

  for(const auto &l : bv)
    if(l.is_false())
      return l;

  if(is_all(bv, const_literal(true)))
    return const_literal(true);

  bvt new_bv=eliminate_duplicates(bv);

  bvt lits(2);
  literalt literal=new_variable();
  lits[1]=neg(literal);

  for(const auto &l : new_bv)
  {
    lits[0]=pos(l);
    lcnf(lits);
  }

  lits.clear();
  lits.reserve(new_bv.size()+1);

  for(const auto &l : new_bv)
    lits.push_back(neg(l));

  lits.push_back(pos(literal));
  lcnf(lits);

  return literal;
}

/// Tseitin encoding of disjunction between multiple literals
/// \par parameters: Any number of inputs to the OR gate
/// \return Output signal of the OR gate as literal
literalt cnft::lor(const bvt &bv)
{
  if(bv.empty())
    return const_literal(false);
  if(bv.size()==1)
    return bv[0];
  if(bv.size()==2)
    return lor(bv[0], bv[1]);

  for(const auto &l : bv)
    if(l.is_true())
      return l;

  if(is_all(bv, const_literal(false)))
    return const_literal(false);

  bvt new_bv=eliminate_duplicates(bv);

  bvt lits(2);
  literalt literal=new_variable();
  lits[1]=pos(literal);

  for(const auto &l : new_bv)
  {
    lits[0]=neg(l);
    lcnf(lits);
  }

  lits.clear();
  lits.reserve(new_bv.size()+1);

  for(const auto &l : new_bv)
    lits.push_back(pos(l));

  lits.push_back(neg(literal));
  lcnf(lits);

  return literal;
}

/// Tseitin encoding of XOR between multiple literals
/// \par parameters: Any number of inputs to the XOR gate
/// \return Output signal of the XOR gate as literal
literalt cnft::lxor(const bvt &bv)
{
  if(bv.empty())
    return const_literal(false);
  if(bv.size()==1)
    return bv[0];
  if(bv.size()==2)
    return lxor(bv[0], bv[1]);

  literalt literal=const_literal(false);

  for(const auto &l : bv)
    literal=lxor(l, literal);

  return literal;
}

/// \par parameters: Two inputs to the AND gate
/// \return Output signal of the AND gate as literal
literalt cnft::land(literalt a, literalt b)
{
  if(a.is_true() || b.is_false())
    return b;
  if(b.is_true() || a.is_false())
    return a;
  if(a==b)
    return a;

  literalt o=new_variable();
  gate_and(a, b, o);
  return o;
}

/// \par parameters: Two inputs to the OR gate
/// \return Output signal of the OR gate as literal
literalt cnft::lor(literalt a, literalt b)
{
  if(a.is_false() || b.is_true())
    return b;
  if(b.is_false() || a.is_true())
    return a;
  if(a==b)
    return a;

  literalt o=new_variable();
  gate_or(a, b, o);
  return o;
}

/// \par parameters: Two inputs to the XOR gate
/// \return Output signal of the XOR gate as literal
literalt cnft::lxor(literalt a, literalt b)
{
  if(a.is_false())
    return b;
  if(b.is_false())
    return a;
  if(a.is_true())
    return !b;
  if(b.is_true())
    return !a;
  if(a==b)
    return const_literal(false);
  if(a==!b)
    return const_literal(true);

  literalt o=new_variable();
  gate_xor(a, b, o);
  return o;
}

/// \par parameters: Two inputs to the NAND gate
/// \return Output signal of the NAND gate as literal
literalt cnft::lnand(literalt a, literalt b)
{
  return !land(a, b);
}

/// \par parameters: Two inputs to the NOR gate
/// \return Output signal of the NOR gate as literal
literalt cnft::lnor(literalt a, literalt b)
{
  return !lor(a, b);
}

literalt cnft::lequal(literalt a, literalt b)
{
  return !lxor(a, b);
}

literalt cnft::limplies(literalt a, literalt b)
{
  return lor(!a, b);
}

// Tino observed slow-downs up to 50% with OPTIMAL_COMPACT_ITE.

#define COMPACT_ITE
// #define OPTIMAL_COMPACT_ITE

literalt cnft::lselect(literalt a, literalt b, literalt c)
{
  // a?b:c = (a AND b) OR (/a AND c)
  if(a.is_constant())
    return a.sign() ? b : c;
  if(b==c)
    return b;

  if(b.is_constant())
    return b.sign() ? lor(a, c) : land(!a, c);
  if(c.is_constant())
    return c.sign() ? lor(!a, b) : land(a, b);

  #ifdef COMPACT_ITE

  // (a+c'+o) (a+c+o') (a'+b'+o) (a'+b+o')

  literalt o=new_variable();

  bvt lits;

  lcnf(a, !c,  o);
  lcnf(a,  c, !o);
  lcnf(!a, !b,  o);
  lcnf(!a,  b, !o);

  #ifdef OPTIMAL_COMPACT_ITE
  // additional clauses to enable better propagation
  lcnf(b,  c, !o);
  lcnf(!b, !c,  o);
  #endif

  return o;

  #else
  return lor(land(a, b), land(!a, c));
  #endif
}

/// Generate a new variable and return it as a literal
/// \return New variable as literal
literalt cnft::new_variable()
{
  literalt l(_no_variables, false);

  set_no_variables(_no_variables+1);

  return l;
}

/// Generate a vector of new variables.
/// \return Vector of new variables.
bvt cnft::new_variables(std::size_t width)
{
  bvt result;
  result.reserve(width);

  for(std::size_t i = _no_variables; i < _no_variables + width; ++i)
    result.emplace_back(i, false);

  set_no_variables(_no_variables + width);

  return result;
}

/// eliminate duplicates from given vector of literals
/// \par parameters: set of literals given as vector
/// \return set of literals, duplicates removed
bvt cnft::eliminate_duplicates(const bvt &bv)
{
  bvt dest = bv;
  std::sort(dest.begin(), dest.end());
  auto last = std::unique(dest.begin(), dest.end());
  dest.erase(last, dest.end());

  return dest;
}

/// filter 'true' from clause, eliminate duplicates, recognise trivially
/// satisfied clauses
bool cnft::process_clause(const bvt &bv, bvt &dest) const
{
  dest.clear();

  // empty clause! this is UNSAT
  if(bv.empty())
    return false;

  // first check simple things

  for(const auto &l : bv)
  {
    // we never use index 0
    INVARIANT(l.var_no() != 0, "variable 0 must not be used");

    // we never use 'unused_var_no'
    INVARIANT(
      l.var_no() != literalt::unused_var_no(),
      "variable 'unused_var_no' must not be used");

    if(l.is_true())
      return true; // clause satisfied

    if(l.is_false())
      continue; // will remove later

    INVARIANT(
      l.var_no() < _no_variables,
      "unknown variable " + std::to_string(l.var_no()) +
        " (no_variables = " + std::to_string(_no_variables) + " )");
  }

  // now copy
  dest.clear();
  dest.reserve(bv.size());

  for(const auto &l : bv)
  {
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

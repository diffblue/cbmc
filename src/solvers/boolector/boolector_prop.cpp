/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#include <assert.h>
#include <i2string.h>
#include <set>

#include "boolector_prop.h"

extern "C" {
#include "include/boolector.h"
}

/*******************************************************************\

Function: boolector_propt::boolector_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolector_propt::boolector_propt()
{
  boolector_ctx=boolector_new();
  _no_variables=0;
}

/*******************************************************************\

Function: boolector_propt::~boolector_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolector_propt::~boolector_propt()
{
  delete boolector_ctx;
}

/*******************************************************************\

Function: boolector_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::land(const bvt &bv)
{
  literalt l=new_variable();
  u_int size=bv.size()+1;
  BtorExp *args[size], *result;

  for(unsigned int i=0; i<bv.size(); i++)
  {
	args[i] = boolector_literal(bv[i]);

    if (i==1)
      result = boolector_and(boolector_ctx, args[0], args[1]);
    else if (i>1)
      result = boolector_and(boolector_ctx, result, args[i]);
  }

  boolector_assert(boolector_ctx, boolector_iff(boolector_ctx, boolector_literal(l), result));

  return l;
}


/*******************************************************************\

Function: boolector_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lor(const bvt &bv)
{
  literalt l=new_variable();
  u_int size=bv.size()+1;
  BtorExp *args[size], *result;

  for(unsigned int i=0; i<bv.size(); i++)
  {
	args[i] = boolector_literal(bv[i]);

    if (i==1)
      result = boolector_or(boolector_ctx, args[0], args[1]);
    else if (i>1)
      result = boolector_or(boolector_ctx, result, args[i]);
  }

  boolector_assert(boolector_ctx, boolector_iff(boolector_ctx, boolector_literal(l), result));

  return l;
}

/*******************************************************************\

Function: boolector_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lxor(const bvt &bv)
{
  if(bv.size()==0) return const_literal(false);
  if(bv.size()==1) return bv[0];

  literalt l=new_variable();
  u_int size=bv.size()+1;
  BtorExp *args[size], *result;

  for(unsigned int i=0; i<bv.size(); i++)
  {
	args[i] = boolector_literal(bv[i]);

    if (i==1)
      result = boolector_xor(boolector_ctx, args[0], args[1]);
    else if (i>1)
      result = boolector_xor(boolector_ctx, result, args[i]);
  }

  boolector_assert(boolector_ctx, boolector_iff(boolector_ctx, boolector_literal(l), result));

  return l;
}

/*******************************************************************\

Function:  boolector_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  literalt l=new_variable();
  BtorExp *result;

  result = boolector_and(boolector_ctx, boolector_literal(a), boolector_literal(b));
  boolector_assert(boolector_ctx, boolector_iff(boolector_ctx, boolector_literal(l), result));

  return l;
}

/*******************************************************************\

Function: boolector_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;

  literalt l=new_variable();
  BtorExp *result;

  result = boolector_or(boolector_ctx, boolector_literal(a), boolector_literal(b));
  boolector_assert(boolector_ctx, boolector_iff(boolector_ctx, boolector_literal(l), result));

  return l;
}

/*******************************************************************\

Function: boolector_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: boolector_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  literalt l=new_variable();
  BtorExp *result;

  result = boolector_xor(boolector_ctx, boolector_literal(a), boolector_literal(b));
  boolector_assert(boolector_ctx, boolector_iff(boolector_ctx, boolector_literal(l), result));


  return l;
}

/*******************************************************************\

Function: boolector_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: boolector_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}


/*******************************************************************\

Function: boolector_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: boolector_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: boolector_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::lselect(literalt a, literalt b, literalt c)
{
  if(a==const_literal(true)) return b;
  if(a==const_literal(false)) return c;
  if(b==c) return b;

  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  literalt l=new_variable();
  BtorExp *result;

  result = boolector_cond(boolector_ctx, boolector_literal(a), boolector_literal(b), boolector_literal(c));
  boolector_assert(boolector_ctx, boolector_iff(boolector_ctx, boolector_literal(l), result));

  return l;
}

/*******************************************************************\

Function: boolector_propt::new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolector_propt::new_variable()
{
  literalt l;
  l.set(_no_variables, false);
  _no_variables++;

  //std::cout << "literal: l" << _no_variables << "\n";

  return l;
}

/*******************************************************************\

Function: boolector_propt::eliminate_duplicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolector_propt::eliminate_duplicates(const bvt &bv, bvt &dest)
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

Function: boolector_propt::process_clause

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool boolector_propt::process_clause(const bvt &bv, bvt &dest)
{
  dest.clear();

  if(bv.empty()) return false;

  std::set<literalt> s;

  dest.reserve(bv.size());

  for(bvt::const_iterator it=bv.begin();
      it!=bv.end();
      it++)
  {
    literalt l=*it;

    if (l.var_no()==0)
    	return true;

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

/*******************************************************************\

Function: boolector_propt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolector_propt::lcnf(const bvt &bv)
{
  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  BtorExp *lor_var, *args[new_bv.size()];
  unsigned int i=0, j=0;

  for(bvt::const_iterator it=new_bv.begin(); it!=new_bv.end(); it++, i++)
	args[i] = boolector_literal(*it);

  if (i>1)
  {
	lor_var = boolector_or(boolector_ctx, args[0], args[1]);

    for(j=2; j<i; j++)
      lor_var = boolector_or(boolector_ctx, args[j], lor_var);

    boolector_assert(boolector_ctx, lor_var);
  }
  else if (i==1)
  {
	boolector_assert(boolector_ctx, args[0]);
  }
}

/*******************************************************************\

Function: boolector_propt::convert_literal
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

BtorExp* boolector_propt::convert_literal(unsigned l)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

  std::string literal_s;

  literal_cachet::const_iterator cache_result=literal_cache.find(l);
  if(cache_result!=literal_cache.end())
  {
    //std::cout << "Cache hit on " << cache_result->first << "\n";
    return cache_result->second;
  }

  BtorExp* result;

  literal_s = "l"+i2string(l);
  result = boolector_var(boolector_ctx, 1, literal_s.c_str());

  // insert into cache
  literal_cache.insert(std::pair<unsigned, BtorExp*>(l, result));

  return result;
}

/*******************************************************************\

Function: boolector_propt::boolector_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

BtorExp* boolector_propt::boolector_literal(literalt l)
{
  BtorExp *literal_l;
  std::string literal_s;

  if(l==const_literal(false))
    return boolector_false(boolector_ctx);
  else if(l==const_literal(true))
	return boolector_true(boolector_ctx);

  literal_l = convert_literal(l.var_no());

  if(l.sign())
    return boolector_not(boolector_ctx, literal_l);

  return literal_l;
}

/*******************************************************************\

Function: boolector_propt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt boolector_propt::prop_solve()
{
  return P_ERROR;
}

/*******************************************************************\

Function: boolector_propt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt boolector_propt::l_get(literalt a) const
{
  tvt result=tvt(false);
  std::string literal;
  BtorExp *boolector_literal;
  size_t found;

  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  literal_cachet::const_iterator cache_result=literal_cache.find(a.var_no());
  if(cache_result!=literal_cache.end())
    boolector_literal = cache_result->second;
  else
	return tvt(tvt::TV_UNKNOWN);

  literal = boolector_bv_assignment(boolector_ctx, boolector_literal);
  found=literal.find("1");

  if (found!=std::string::npos)
    result=tvt(true);
  else
	result=tvt(false);

  if (a.sign()) result=!result;

  return result;
}

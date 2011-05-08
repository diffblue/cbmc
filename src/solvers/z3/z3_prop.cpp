/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#include <assert.h>
#include <set>
#include <i2string.h>

#include "z3_prop.h"

/*******************************************************************\

Function: z3_propt::z3_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3_propt::z3_propt(std::ostream &_out):out(_out)
{
  _no_variables=1;
}

/*******************************************************************\

Function: z3_propt::~z3_propt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3_propt::~z3_propt()
{
}

/*******************************************************************\

Function: z3_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::land(literalt a, literalt b, literalt o)
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

Function: z3_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::lor(literalt a, literalt b, literalt o)
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

Function: z3_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::lxor(literalt a, literalt b, literalt o)
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

Function: z3_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::lnand(literalt a, literalt b, literalt o)
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

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::lnor(literalt a, literalt b, literalt o)
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

Function: z3_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::lequal(literalt a, literalt b, literalt o)
{
  lxor(a, b, lnot(o));
}

/*******************************************************************\

Function: z3_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::limplies(literalt a, literalt b, literalt o)
{
  lor(lnot(a), b, o);
}

/*******************************************************************\

Function: z3_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::land(const bvt &bv)
{
  if(bv.size()==0) return const_literal(true);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return land(bv[0], bv[1]);

  for(unsigned i=0; i<bv.size(); i++)
    if(bv[i]==const_literal(false))
      return const_literal(false);

  if(is_all(bv, const_literal(true)))
    return const_literal(true);

  bvt new_bv;

  eliminate_duplicates(bv, new_bv);

  literalt literal=new_variable();

  for(unsigned int i=0; i<new_bv.size(); ++i)
  {
    bvt lits;
    lits.reserve(2);
    lits.push_back(pos(new_bv[i]));
    lits.push_back(neg(literal));
    lcnf(lits);
  }

  bvt lits;
  lits.reserve(new_bv.size()+1);

  for(unsigned int i=0; i<new_bv.size(); ++i)
    lits.push_back(neg(new_bv[i]));

  lits.push_back(pos(literal));
  lcnf(lits);

  return literal;
}

/*******************************************************************\

Function: z3_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lor(const bvt &bv)
{
  if(bv.size()==0) return const_literal(false);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return lor(bv[0], bv[1]);

  for(unsigned i=0; i<bv.size(); i++)
    if(bv[i]==const_literal(true))
      return const_literal(true);

  if(is_all(bv, const_literal(false)))
    return const_literal(false);

  bvt new_bv;

  eliminate_duplicates(bv, new_bv);

  literalt literal=new_variable();

  for(unsigned int i=0; i<new_bv.size(); ++i)
  {
    bvt lits;
    lits.reserve(2);
    lits.push_back(neg(new_bv[i]));
    lits.push_back(pos(literal));
    lcnf(lits);
  }

  bvt lits;
  lits.reserve(new_bv.size()+1);

  for(unsigned int i=0; i<new_bv.size(); ++i)
    lits.push_back(pos(new_bv[i]));

  lits.push_back(neg(literal));
  lcnf(lits);

  return literal;
}

/*******************************************************************\

Function: z3_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lxor(const bvt &bv)
{
  if(bv.size()==0) return const_literal(false);
  if(bv.size()==1) return bv[0];
  if(bv.size()==2) return lxor(bv[0], bv[1]);

  literalt literal=const_literal(false);

  for(unsigned i=0; i<bv.size(); i++)
    literal=lxor(bv[i], literal);

  return literal;
}
/*******************************************************************\

Function: z3_propt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  literalt o=new_variable();
  land(a, b, o);
  return o;
}

/*******************************************************************\

Function: z3_propt::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;

  literalt o=new_variable();
  lor(a, b, o);
  return o;
}

/*******************************************************************\

Function: z3_propt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lnot(literalt a)
{
  a.invert();

  return a;
}

/*******************************************************************\

Function: z3_propt::lxor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lxor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return lnot(b);
  if(b==const_literal(true)) return lnot(a);

  literalt o=new_variable();
  lxor(a, b, o);
  return o;
}

/*******************************************************************\

Function: z3_propt::lnand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lnand(literalt a, literalt b)
{
  return lnot(land(a, b));
}

/*******************************************************************\

Function: z3_propt::lnor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lnor(literalt a, literalt b)
{
  return lnot(lor(a, b));
}

/*******************************************************************\

Function: z3_propt::lequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lequal(literalt a, literalt b)
{
  return lnot(lxor(a, b));
}

/*******************************************************************\

Function: z3_propt::limplies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::limplies(literalt a, literalt b)
{
  return lor(lnot(a), b);
}

/*******************************************************************\

Function: z3_propt::lselect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::lselect(literalt a, literalt b, literalt c)
{
  // a?b:c = (a AND b) OR (/a AND c)
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

Function: z3_propt::new_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_propt::new_variable()
{
  literalt l;

  l.set(_no_variables, false);

  set_no_variables(_no_variables+1);

#ifdef DEBUG
  //std::cout << "new literal: l" << l.var_no() << "\n";
#endif

  return l;
}

/*******************************************************************\

Function: z3_propt::eliminate_duplicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::eliminate_duplicates(const bvt &bv, bvt &dest)
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

Function: z3_propt::process_clause

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool z3_propt::process_clause(const bvt &bv, bvt &dest)
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

Function: z3_propt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_propt::lcnf(const bvt &bv)
{
  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  if (new_bv.size()==0)
    return;

  Z3_ast lor_var, args[new_bv.size()];
  unsigned int i=0;

  for(bvt::const_iterator it=new_bv.begin(); it!=new_bv.end(); it++, i++)
	args[i] = z3_literal(*it);

  if (i>1)
  {
    lor_var = Z3_mk_or(z3_ctx, i, args);
    Z3_assert_cnstr(z3_ctx, lor_var);
  }
  else
  {
	Z3_assert_cnstr(z3_ctx, args[0]);
  }
}

/*******************************************************************\

Function: z3_propt::z3_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

Z3_ast z3_propt::z3_literal(literalt l)
{
  Z3_ast literal_l;
  std::string literal_s;

  if(l==const_literal(false))
    return Z3_mk_false(z3_ctx);
  else if(l==const_literal(true))
    return Z3_mk_true(z3_ctx);

  literal_s = "l"+i2string(l.var_no());
#ifdef DEBUG
  std::cout << "literal_s: " << literal_s << "\n";
#endif
  literal_l = z3_api.mk_bool_var(z3_ctx, literal_s.c_str());

  if(l.sign())
  {
    return Z3_mk_not(z3_ctx, literal_l);
  }

  return literal_l;
}

/*******************************************************************\

Function: z3_propt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt z3_propt::prop_solve()
{
  return P_ERROR;
}

/*******************************************************************\

Function: z3_propt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt z3_propt::l_get(literalt a) const
{
  tvt result=tvt(false);
  std::string literal;
  Z3_ast z3_literal;
  size_t found;

  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  literal = "l"+i2string(a.var_no());

  map_prop_varst::const_iterator cache_result=map_prop_vars.find(literal.c_str());
  if(cache_result!=map_prop_vars.end())
  {
    //std::cout << "Cache hit on " << cache_result->first << "\n";
	z3_literal = cache_result->second;
    Z3_app app = Z3_to_app(z3_ctx, z3_literal);
    Z3_func_decl d = Z3_get_app_decl(z3_ctx, app);
    literal = Z3_func_decl_to_string(z3_ctx, d);

    found=literal.find("true");

    if (found!=std::string::npos)
      result=tvt(true);
    else
      result=tvt(false);
  }

  if (a.sign()) result=!result;

  return result;
}

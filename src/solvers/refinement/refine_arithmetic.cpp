/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_refinement.h"

#include <util/bv_arithmetic.h>
#include <util/ieee_float.h>
#include <util/expr_util.h>
#include <util/arith_tools.h>

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/floatbv/float_utils.h>

// Parameters
#define MAX_INTEGER_UNDERAPPROX 3
#define MAX_FLOAT_UNDERAPPROX 10

void bv_refinementt::approximationt::add_over_assumption(literalt l)
{
  // if it's a constant already, give up
  if(!l.is_constant())
    over_assumptions.push_back(l);
}

void bv_refinementt::approximationt::add_under_assumption(literalt l)
{
  // if it's a constant already, give up
  if(!l.is_constant())
    under_assumptions.push_back(l);
}

bvt bv_refinementt::convert_floatbv_op(const exprt &expr)
{
  if(!config_.refine_arithmetic)
    return SUB::convert_floatbv_op(expr);

  if(ns.follow(expr.type()).id()!=ID_floatbv ||
     expr.operands().size()!=3)
    return SUB::convert_floatbv_op(expr);

  bvt bv;
  add_approximation(expr, bv);
  return bv;
}

bvt bv_refinementt::convert_mult(const mult_exprt &expr)
{
  if(!config_.refine_arithmetic || expr.type().id()==ID_fixedbv)
    return SUB::convert_mult(expr);

  // we catch any multiplication
  // unless it involves a constant

  const exprt::operandst &operands=expr.operands();

  const typet &type=ns.follow(expr.type());

  PRECONDITION(operands.size()>=2);

  if(operands.size()>2)
    return convert_mult(to_mult_expr(make_binary(expr))); // make binary

  // we keep multiplication by a constant for integers
  if(type.id()!=ID_floatbv)
    if(operands[0].is_constant() || operands[1].is_constant())
      return SUB::convert_mult(expr);

  bvt bv;
  approximationt &a=add_approximation(expr, bv);

  // initially, we have a partial interpretation for integers
  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv)
  {
    // x*0==0 and 0*x==0
    literalt op0_zero=bv_utils.is_zero(a.op0_bv);
    literalt op1_zero=bv_utils.is_zero(a.op1_bv);
    literalt res_zero=bv_utils.is_zero(a.result_bv);
    prop.l_set_to_true(
      prop.limplies(prop.lor(op0_zero, op1_zero), res_zero));

    // x*1==x and 1*x==x
    literalt op0_one=bv_utils.is_one(a.op0_bv);
    literalt op1_one=bv_utils.is_one(a.op1_bv);
    literalt res_op0=bv_utils.equal(a.op0_bv, a.result_bv);
    literalt res_op1=bv_utils.equal(a.op1_bv, a.result_bv);
    prop.l_set_to_true(prop.limplies(op0_one, res_op1));
    prop.l_set_to_true(prop.limplies(op1_one, res_op0));
  }

  return bv;
}

bvt bv_refinementt::convert_div(const div_exprt &expr)
{
  if(!config_.refine_arithmetic || expr.type().id()==ID_fixedbv)
    return SUB::convert_div(expr);

  // we catch any division
  // unless it's integer division by a constant

  PRECONDITION(expr.operands().size()==2);

  if(expr.op1().is_constant())
    return SUB::convert_div(expr);

  bvt bv;
  add_approximation(expr, bv);
  return bv;
}

bvt bv_refinementt::convert_mod(const mod_exprt &expr)
{
  if(!config_.refine_arithmetic || expr.type().id()==ID_fixedbv)
    return SUB::convert_mod(expr);

  // we catch any mod
  // unless it's integer + constant

  PRECONDITION(expr.operands().size()==2);

  if(expr.op1().is_constant())
    return SUB::convert_mod(expr);

  bvt bv;
  add_approximation(expr, bv);
  return bv;
}

void bv_refinementt::get_values(approximationt &a)
{
  std::size_t o=a.expr.operands().size();

  if(o==1)
    a.op0_value=get_value(a.op0_bv);
  else if(o==2)
  {
    a.op0_value=get_value(a.op0_bv);
    a.op1_value=get_value(a.op1_bv);
  }
  else if(o==3)
  {
    a.op0_value=get_value(a.op0_bv);
    a.op1_value=get_value(a.op1_bv);
    a.op2_value=get_value(a.op2_bv);
  }
  else
    UNREACHABLE;

  a.result_value=get_value(a.result_bv);
}

/// inspect if satisfying assignment extends to original formula, otherwise
/// refine overapproximation
void bv_refinementt::check_SAT(approximationt &a)
{
  // get values
  get_values(a);

  // see if the satisfying assignment is spurious in any way

  const typet &type=ns.follow(a.expr.type());

  if(type.id()==ID_floatbv)
  {
    // these are all ternary
    INVARIANT(
      a.expr.operands().size()==3,
      string_refinement_invariantt("all floatbv typed exprs are ternary"));

    if(a.over_state==MAX_STATE)
      return;

    ieee_float_spect spec(to_floatbv_type(type));
    ieee_floatt o0(spec), o1(spec);

    o0.unpack(a.op0_value);
    o1.unpack(a.op1_value);

    // get actual rounding mode
    exprt rounding_mode_expr = get(a.expr.op2());
    const std::size_t rounding_mode_int =
      numeric_cast_v<std::size_t>(rounding_mode_expr);
    ieee_floatt::rounding_modet rounding_mode =
      (ieee_floatt::rounding_modet)rounding_mode_int;

    ieee_floatt result=o0;
    o0.rounding_mode=rounding_mode;
    o1.rounding_mode=rounding_mode;
    result.rounding_mode=rounding_mode;

    if(a.expr.id()==ID_floatbv_plus)
      result+=o1;
    else if(a.expr.id()==ID_floatbv_minus)
      result-=o1;
    else if(a.expr.id()==ID_floatbv_mult)
      result*=o1;
    else if(a.expr.id()==ID_floatbv_div)
      result/=o1;
    else
      UNREACHABLE;

    if(result.pack()==a.result_value) // ok
      return;

    #ifdef DEBUG
    ieee_floatt rr(spec);
    rr.unpack(a.result_value);

    debug() << "S1: " << o0 << " " << a.expr.id() << " " << o1
              << " != " << rr << eom;
    debug() << "S2: " << integer2binary(a.op0_value, spec.width())
                        << " " << a.expr.id() << " " <<
                           integer2binary(a.op1_value, spec.width())
              << "!=" << integer2binary(a.result_value, spec.width()) << eom;
    debug() << "S3: " << integer2binary(a.op0_value, spec.width())
                        << " " << a.expr.id() << " " <<
                           integer2binary(a.op1_value, spec.width())
              << "==" << integer2binary(result.pack(), spec.width()) << eom;
    #endif

    if(a.over_state<config_.max_node_refinement)
    {
      bvt r;
      float_utilst float_utils(prop);
      float_utils.spec=spec;
      float_utils.rounding_mode_bits.set(rounding_mode);

      literalt op0_equal=
        bv_utils.equal(a.op0_bv, float_utils.build_constant(o0));

      literalt op1_equal=
        bv_utils.equal(a.op1_bv, float_utils.build_constant(o1));

      literalt result_equal=
        bv_utils.equal(a.result_bv, float_utils.build_constant(result));

      literalt op0_and_op1_equal=
        prop.land(op0_equal, op1_equal);

      prop.l_set_to_true(
        prop.limplies(op0_and_op1_equal, result_equal));
    }
    else
    {
      // give up
      // remove any previous over-approximation
      a.over_assumptions.clear();
      a.over_state=MAX_STATE;

      bvt r;
      float_utilst float_utils(prop);
      float_utils.spec=spec;
      float_utils.rounding_mode_bits.set(rounding_mode);

      bvt op0=a.op0_bv, op1=a.op1_bv, res=a.result_bv;

      if(a.expr.id()==ID_floatbv_plus)
        r=float_utils.add(op0, op1);
      else if(a.expr.id()==ID_floatbv_minus)
        r=float_utils.sub(op0, op1);
      else if(a.expr.id()==ID_floatbv_mult)
        r=float_utils.mul(op0, op1);
      else if(a.expr.id()==ID_floatbv_div)
        r=float_utils.div(op0, op1);
      else
        UNREACHABLE;

      CHECK_RETURN(r.size()==res.size());
      bv_utils.set_equal(r, res);
    }
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv)
  {
    // these are all binary
    INVARIANT(
      a.expr.operands().size()==2,
      string_refinement_invariantt("all (un)signedbv typed exprs are binary"));

    // already full interpretation?
    if(a.over_state>0)
      return;

    bv_spect spec(type);
    bv_arithmetict o0(spec), o1(spec);
    o0.unpack(a.op0_value);
    o1.unpack(a.op1_value);

    // division by zero is never spurious

    if((a.expr.id()==ID_div || a.expr.id()==ID_mod) &&
       o1==0)
      return;

    if(a.expr.id()==ID_mult)
      o0*=o1;
    else if(a.expr.id()==ID_div)
      o0/=o1;
    else if(a.expr.id()==ID_mod)
      o0%=o1;
    else
      UNREACHABLE;

    if(o0.pack()==a.result_value) // ok
      return;

    if(a.over_state==0)
    {
      // we give up right away and add the full interpretation
      bvt r;
      if(a.expr.id()==ID_mult)
      {
        r=bv_utils.multiplier(
          a.op0_bv, a.op1_bv,
          a.expr.type().id()==ID_signedbv?
            bv_utilst::representationt::SIGNED:
            bv_utilst::representationt::UNSIGNED);
      }
      else if(a.expr.id()==ID_div)
      {
        r=bv_utils.divider(
          a.op0_bv, a.op1_bv,
          a.expr.type().id()==ID_signedbv?
            bv_utilst::representationt::SIGNED:
            bv_utilst::representationt::UNSIGNED);
      }
      else if(a.expr.id()==ID_mod)
      {
        r=bv_utils.remainder(
          a.op0_bv, a.op1_bv,
          a.expr.type().id()==ID_signedbv?
            bv_utilst::representationt::SIGNED:
            bv_utilst::representationt::UNSIGNED);
      }
      else
        UNREACHABLE;

      bv_utils.set_equal(r, a.result_bv);
    }
    else
      UNREACHABLE;
  }
  else if(type.id()==ID_fixedbv)
  {
    // TODO: not implemented
    TODO;
  }
  else
  {
    UNREACHABLE;
  }

  status() << "Found spurious `" << a.as_string()
           << "' (state " << a.over_state << ")" << eom;

  progress=true;
  if(a.over_state<MAX_STATE)
    a.over_state++;
}

/// inspect if proof holds on original formula, otherwise refine
/// underapproximation
void bv_refinementt::check_UNSAT(approximationt &a)
{
  // part of the conflict?
  if(!this->conflicts_with(a))
    return;

  status() << "Found assumption for `" << a.as_string()
           << "' in proof (state " << a.under_state << ")" << eom;

  PRECONDITION(!a.under_assumptions.empty());

  a.under_assumptions.clear();

  if(a.expr.type().id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=to_floatbv_type(a.expr.type());
    ieee_float_spect spec(floatbv_type);

    a.under_assumptions.reserve(a.op0_bv.size()+a.op1_bv.size());

    float_utilst float_utils(prop);
    float_utils.spec=spec;

    // the fraction without hidden bit
    const bvt fraction0=float_utils.get_fraction(a.op0_bv);
    const bvt fraction1=float_utils.get_fraction(a.op1_bv);

    if(a.under_state==0)
    {
      // we first set sign and exponent free,
      // but keep the fraction zero

      for(std::size_t i=0; i<fraction0.size(); i++)
        a.add_under_assumption(!fraction0[i]);

      for(std::size_t i=0; i<fraction1.size(); i++)
        a.add_under_assumption(!fraction1[i]);
    }
    else
    {
      // now fraction: make this grow quadratically
      unsigned x=a.under_state*a.under_state;

      if(x>=MAX_FLOAT_UNDERAPPROX && x>=a.result_bv.size())
      {
        // make it free altogether, this guarantees progress
      }
      else
      {
        // set x bits of both exponent and mantissa free
        // need to start with most-significant bits

        #if 0
        for(std::size_t i=x; i<fraction0.size(); i++)
          a.add_under_assumption(!fraction0[fraction0.size()-i-1]);

        for(std::size_t i=x; i<fraction1.size(); i++)
          a.add_under_assumption(!fraction1[fraction1.size()-i-1]);
        #endif
      }
    }
  }
  else
  {
    unsigned x=a.under_state+1;

    if(x>=MAX_INTEGER_UNDERAPPROX && x>=a.result_bv.size())
    {
      // make it free altogether, this guarantees progress
    }
    else
    {
      // set x least-significant bits free
      a.under_assumptions.reserve(a.op0_bv.size()+a.op1_bv.size());

      for(std::size_t i=x; i<a.op0_bv.size(); i++)
        a.add_under_assumption(!a.op0_bv[i]);

      for(std::size_t i=x; i<a.op1_bv.size(); i++)
        a.add_under_assumption(!a.op1_bv[i]);
    }
  }

  a.under_state++;
  progress=true;
}

/// check if an under-approximation is part of the conflict
bool bv_refinementt::conflicts_with(approximationt &a)
{
  for(std::size_t i=0; i<a.under_assumptions.size(); i++)
    if(prop.is_in_conflict(a.under_assumptions[i]))
      return true;

  return false;
}

void bv_refinementt::initialize(approximationt &a)
{
  a.over_state=a.under_state=0;

  a.under_assumptions.reserve(a.op0_bv.size()+a.op1_bv.size());

  // initially, we force the operands to be all zero

  for(std::size_t i=0; i<a.op0_bv.size(); i++)
    a.add_under_assumption(!a.op0_bv[i]);

  for(std::size_t i=0; i<a.op1_bv.size(); i++)
    a.add_under_assumption(!a.op1_bv[i]);
}

bv_refinementt::approximationt &
bv_refinementt::add_approximation(
  const exprt &expr, bvt &bv)
{
  approximations.push_back(approximationt(approximations.size()));
  approximationt &a=approximations.back();

  std::size_t width=boolbv_width(expr.type());
  PRECONDITION(width!=0);

  a.expr=expr;
  a.result_bv=prop.new_variables(width);
  a.no_operands=expr.operands().size();
  set_frozen(a.result_bv);

  if(a.no_operands==1)
  {
    a.op0_bv=convert_bv(expr.op0());
    set_frozen(a.op0_bv);
  }
  else if(a.no_operands==2)
  {
    a.op0_bv=convert_bv(expr.op0());
    a.op1_bv=convert_bv(expr.op1());
    set_frozen(a.op0_bv);
    set_frozen(a.op1_bv);
  }
  else if(a.no_operands==3)
  {
    a.op0_bv=convert_bv(expr.op0());
    a.op1_bv=convert_bv(expr.op1());
    a.op2_bv=convert_bv(expr.op2());
    set_frozen(a.op0_bv);
    set_frozen(a.op1_bv);
    set_frozen(a.op2_bv);
  }
  else
    UNREACHABLE;

  bv=a.result_bv;

  initialize(a);

  return a;
}

std::string bv_refinementt::approximationt::as_string() const
{
  return std::to_string(id_nr)+"/"+id2string(expr.id());
}

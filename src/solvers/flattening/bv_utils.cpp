/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_utils.h"

#include <cassert>

#include <util/arith_tools.h>

bvt bv_utilst::build_constant(const mp_integer &n, std::size_t width)
{
  std::string n_str=integer2binary(n, width);
  CHECK_RETURN(n_str.size() == width);
  bvt result;
  result.resize(width);
  for(std::size_t i=0; i<width; i++)
    result[i]=const_literal(n_str[width-i-1]=='1');
  return result;
}

literalt bv_utilst::is_one(const bvt &bv)
{
  PRECONDITION(!bv.empty());
  bvt tmp;
  tmp=bv;
  tmp.erase(tmp.begin(), tmp.begin()+1);
  return prop.land(is_zero(tmp), bv[0]);
}

void bv_utilst::set_equal(const bvt &a, const bvt &b)
{
  PRECONDITION(a.size() == b.size());
  for(std::size_t i=0; i<a.size(); i++)
    prop.set_equal(a[i], b[i]);
}

bvt bv_utilst::extract(const bvt &a, std::size_t first, std::size_t last)
{
  // preconditions
  PRECONDITION(first < a.size());
  PRECONDITION(last < a.size());
  PRECONDITION(first <= last);

  bvt result=a;
  result.resize(last+1);
  if(first!=0)
    result.erase(result.begin(), result.begin()+first);

  POSTCONDITION(result.size() == last - first + 1);
  return result;
}

bvt bv_utilst::extract_msb(const bvt &a, std::size_t n)
{
  // preconditions
  PRECONDITION(n <= a.size());

  bvt result=a;
  result.erase(result.begin(), result.begin()+(result.size()-n));

  POSTCONDITION(result.size() == n);
  return result;
}

bvt bv_utilst::extract_lsb(const bvt &a, std::size_t n)
{
  // preconditions
  PRECONDITION(n <= a.size());

  bvt result=a;
  result.resize(n);
  return result;
}

bvt bv_utilst::concatenate(const bvt &a, const bvt &b) const
{
  bvt result;

  result.resize(a.size()+b.size());

  for(std::size_t i=0; i<a.size(); i++)
    result[i]=a[i];

  for(std::size_t i=0; i<b.size(); i++)
    result[i+a.size()]=b[i];

  return result;
}

/// If s is true, selects a otherwise selects b
bvt bv_utilst::select(literalt s, const bvt &a, const bvt &b)
{
  PRECONDITION(a.size() == b.size());

  bvt result;

  result.resize(a.size());
  for(std::size_t i=0; i<result.size(); i++)
    result[i]=prop.lselect(s, a[i], b[i]);

  return result;
}

bvt bv_utilst::extension(
  const bvt &bv,
  std::size_t new_size,
  representationt rep)
{
  std::size_t old_size=bv.size();
  PRECONDITION(old_size != 0);

  bvt result=bv;
  result.resize(new_size);

  literalt extend_with=
    (rep==representationt::SIGNED && !bv.empty())?bv[old_size-1]:
    const_literal(false);

  for(std::size_t i=old_size; i<new_size; i++)
    result[i]=extend_with;

  return result;
}


/// Generates the encoding of a full adder.  The optimal encoding is the
/// default.
/// \par parameters: a, b, carry_in are the literals representing inputs
/// \return return value is the literal for the sum, carry_out gets the output
///   carry
// The optimal encoding is the default as it gives a reduction in space
// and small performance gains
#define OPTIMAL_FULL_ADDER

literalt bv_utilst::full_adder(
  const literalt a,
  const literalt b,
  const literalt carry_in,
  literalt &carry_out)
{
  #ifdef OPTIMAL_FULL_ADDER
  if(prop.has_set_to() && prop.cnf_handled_well())
  {
    literalt x;
    literalt y;
    int constantProp = -1;

    if(a.is_constant())
    {
      x = b;
      y = carry_in;
      constantProp = (a.is_true()) ? 1 : 0;
    }
    else if(b.is_constant())
    {
      x = a;
      y = carry_in;
      constantProp = (b.is_true()) ? 1 : 0;
    }
    else if(carry_in.is_constant())
    {
      x = a;
      y = b;
      constantProp = (carry_in.is_true()) ? 1 : 0;
    }

    literalt sum;

    // Rely on prop.l* to do further constant propagation
    if(constantProp == 1)
    {
      // At least one input bit is 1
      carry_out = prop.lor(x, y);
      sum = prop.lequal(x, y);
    }
    else if(constantProp == 0)
    {
      // At least one input bit is 0
      carry_out = prop.land(x, y);
      sum = prop.lxor(x, y);
    }
    else
    {
      carry_out = prop.new_variable();
      sum = prop.new_variable();

      // Any two inputs 1 will set the carry_out to 1
      prop.lcnf(!a,        !b, carry_out);
      prop.lcnf(!a, !carry_in, carry_out);
      prop.lcnf(!b, !carry_in, carry_out);

      // Any two inputs 0 will set the carry_out to 0
      prop.lcnf(a,        b, !carry_out);
      prop.lcnf(a, carry_in, !carry_out);
      prop.lcnf(b, carry_in, !carry_out);

      // If both carry out and sum are 1 then all inputs are 1
      prop.lcnf(a, !sum, !carry_out);
      prop.lcnf(b, !sum, !carry_out);
      prop.lcnf(carry_in, !sum, !carry_out);

      // If both carry out and sum are 0 then all inputs are 0
      prop.lcnf(!a, sum, carry_out);
      prop.lcnf(!b, sum, carry_out);
      prop.lcnf(!carry_in, sum, carry_out);

      // If all of the inputs are 1 or all are 0 it sets the sum
      prop.lcnf(!a, !b, !carry_in,  sum);
      prop.lcnf(a,  b,  carry_in, !sum);
    }

    return sum;
  }
  else // NOLINT(readability/braces)
  #endif // OPTIMAL_FULL_ADDER
  {
    // trivial encoding
    carry_out=carry(a, b, carry_in);
    return prop.lxor(prop.lxor(a, b), carry_in);
  }
}

// Daniel's carry optimisation
#define COMPACT_CARRY

literalt bv_utilst::carry(literalt a, literalt b, literalt c)
{
  #ifdef COMPACT_CARRY
  if(prop.has_set_to() && prop.cnf_handled_well())
  {
    // propagation possible?
    const auto const_count =
      a.is_constant() + b.is_constant() + c.is_constant();

    // propagation is possible if two or three inputs are constant
    if(const_count>=2)
      return prop.lor(prop.lor(
          prop.land(a, b),
          prop.land(a, c)),
          prop.land(b, c));

    // it's also possible if two of a,b,c are the same
    if(a==b)
      return a;
    else if(a==c)
      return a;
    else if(b==c)
      return b;

    // the below yields fewer clauses and variables,
    // but doesn't propagate anything at all

    bvt clause;

    literalt x=prop.new_variable();

    /*
    carry_correct: LEMMA
      (    a OR     b OR          NOT x) AND
      (    a OR NOT b OR     c OR NOT x) AND
      (    a OR NOT b OR NOT c OR     x) AND
      (NOT a OR     b OR     c OR NOT x) AND
      (NOT a OR     b OR NOT c OR     x) AND
      (NOT a OR NOT b OR              x)
      IFF
      (x=((a AND b) OR (a AND c) OR (b AND c)));
    */

    prop.lcnf(a,  b,     !x);
    prop.lcnf(a, !b,  c, !x);
    prop.lcnf(a, !b, !c,  x);
    prop.lcnf(!a,  b,  c, !x);
    prop.lcnf(!a,  b, !c,  x);
    prop.lcnf(!a, !b,      x);

    return x;
  }
  else
  #endif // COMPACT_CARRY
  {
    // trivial encoding
    bvt tmp;

    tmp.push_back(prop.land(a, b));
    tmp.push_back(prop.land(a, c));
    tmp.push_back(prop.land(b, c));

    return prop.lor(tmp);
  }
}

void bv_utilst::adder(
  bvt &sum,
  const bvt &op,
  literalt carry_in,
  literalt &carry_out)
{
  PRECONDITION(sum.size() == op.size());

  carry_out=carry_in;

  for(std::size_t i=0; i<sum.size(); i++)
  {
    sum[i] = full_adder(sum[i], op[i], carry_out, carry_out);
  }
}

literalt bv_utilst::carry_out(
  const bvt &op0,
  const bvt &op1,
  literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());

  literalt carry_out=carry_in;

  for(std::size_t i=0; i<op0.size(); i++)
    carry_out=carry(op0[i], op1[i], carry_out);

  return carry_out;
}

bvt bv_utilst::add_sub_no_overflow(
  const bvt &op0,
  const bvt &op1,
  bool subtract,
  representationt rep)
{
  bvt sum=op0;
  adder_no_overflow(sum, op1, subtract, rep);
  return sum;
}

bvt bv_utilst::add_sub(const bvt &op0, const bvt &op1, bool subtract)
{
  PRECONDITION(op0.size() == op1.size());

  literalt carry_in=const_literal(subtract);
  literalt carry_out;

  bvt result=op0;
  bvt tmp_op1=subtract?inverted(op1):op1;

  adder(result, tmp_op1, carry_in, carry_out);

  return result;
}

bvt bv_utilst::add_sub(const bvt &op0, const bvt &op1, literalt subtract)
{
  const bvt op1_sign_applied=
    select(subtract, inverted(op1), op1);

  bvt result=op0;
  literalt carry_out;

  adder(result, op1_sign_applied, subtract, carry_out);

  return result;
}

literalt bv_utilst::overflow_add(
  const bvt &op0, const bvt &op1, representationt rep)
{
  if(rep==representationt::SIGNED)
  {
    // An overflow occurs if the signs of the two operands are the same
    // and the sign of the sum is the opposite.

    literalt old_sign=op0[op0.size()-1];
    literalt sign_the_same=prop.lequal(op0[op0.size()-1], op1[op1.size()-1]);

    bvt result=add(op0, op1);
    return
      prop.land(sign_the_same, prop.lxor(result[result.size()-1], old_sign));
  }
  else if(rep==representationt::UNSIGNED)
  {
    // overflow is simply carry-out
    return carry_out(op0, op1, const_literal(false));
  }
  else
    UNREACHABLE;
}

literalt bv_utilst::overflow_sub(
  const bvt &op0, const bvt &op1, representationt rep)
{
  if(rep==representationt::SIGNED)
  {
    // We special-case x-INT_MIN, which is >=0 if
    // x is negative, always representable, and
    // thus not an overflow.
    literalt op1_is_int_min=is_int_min(op1);
    literalt op0_is_negative=op0[op0.size()-1];

    return
      prop.lselect(op1_is_int_min,
        !op0_is_negative,
        overflow_add(op0, negate(op1), representationt::SIGNED));
  }
  else if(rep==representationt::UNSIGNED)
  {
    // overflow is simply _negated_ carry-out
    return !carry_out(op0, inverted(op1), const_literal(true));
  }
  else
    UNREACHABLE;
}

void bv_utilst::adder_no_overflow(
  bvt &sum,
  const bvt &op,
  bool subtract,
  representationt rep)
{
  const bvt tmp_op=subtract?inverted(op):op;

  if(rep==representationt::SIGNED)
  {
    // an overflow occurs if the signs of the two operands are the same
    // and the sign of the sum is the opposite

    literalt old_sign=sum[sum.size()-1];
    literalt sign_the_same=
      prop.lequal(sum[sum.size()-1], tmp_op[tmp_op.size()-1]);

    literalt carry;
    adder(sum, tmp_op, const_literal(subtract), carry);

    // result of addition in sum
    prop.l_set_to_false(
      prop.land(sign_the_same, prop.lxor(sum[sum.size()-1], old_sign)));
  }
  else
  {
    INVARIANT(
      rep == representationt::UNSIGNED,
      "representation has either value signed or unsigned");
    literalt carry_out;
    adder(sum, tmp_op, const_literal(subtract), carry_out);
    prop.l_set_to(carry_out, subtract);
  }
}

void bv_utilst::adder_no_overflow(bvt &sum, const bvt &op)
{
  literalt carry_out=const_literal(false);

  adder(sum, op, carry_out, carry_out);

  prop.l_set_to_false(carry_out); // enforce no overflow
}

bvt bv_utilst::shift(const bvt &op, const shiftt s, const bvt &dist)
{
  std::size_t d=1, width=op.size();
  bvt result=op;

  for(std::size_t stage=0; stage<dist.size(); stage++)
  {
    if(dist[stage]!=const_literal(false))
    {
      bvt tmp=shift(result, s, d);

      for(std::size_t i=0; i<width; i++)
        result[i]=prop.lselect(dist[stage], tmp[i], result[i]);
    }

    d=d<<1;
  }

  return result;
}

bvt bv_utilst::shift(const bvt &src, const shiftt s, std::size_t dist)
{
  bvt result;
  result.resize(src.size());

  // 'dist' is user-controlled, and thus arbitary.
  // We thus must guard against the case in which i+dist overflows.
  // We do so by considering the case dist>=src.size().

  for(std::size_t i=0; i<src.size(); i++)
  {
    literalt l;

    switch(s)
    {
    case shiftt::SHIFT_LEFT:
      // no underflow on i-dist because of condition dist<=i
      l=(dist<=i?src[i-dist]:const_literal(false));
      break;

    case shiftt::SHIFT_ARIGHT:
      // src.size()-i won't underflow as i<src.size()
      // Then, if dist<src.size()-i, then i+dist<src.size()
      l=(dist<src.size()-i?src[i+dist]:src[src.size()-1]); // sign bit
      break;

    case shiftt::SHIFT_LRIGHT:
      // src.size()-i won't underflow as i<src.size()
      // Then, if dist<src.size()-i, then i+dist<src.size()
      l=(dist<src.size()-i?src[i+dist]:const_literal(false));
      break;

    case shiftt::ROTATE_LEFT:
      // prevent overflows by using dist%src.size()
      l=src[(src.size()+i-(dist%src.size()))%src.size()];
      break;

    case shiftt::ROTATE_RIGHT:
      // prevent overflows by using dist%src.size()
      l=src[(i+(dist%src.size()))%src.size()];
      break;

    default:
      UNREACHABLE;
    }

    result[i]=l;
  }

  return result;
}

bvt bv_utilst::negate(const bvt &bv)
{
  bvt result=inverted(bv);
  literalt carry_out;
  incrementer(result, const_literal(true), carry_out);
  return result;
}

bvt bv_utilst::negate_no_overflow(const bvt &bv)
{
  prop.l_set_to(overflow_negate(bv), false);
  return negate(bv);
}

literalt bv_utilst::overflow_negate(const bvt &bv)
{
  // a overflow on unary- can only happen with the smallest
  // representable number 100....0

  bvt zeros(bv);
  zeros.erase(--zeros.end());

  return prop.land(bv[bv.size()-1], !prop.lor(zeros));
}

void bv_utilst::incrementer(
  bvt &bv,
  literalt carry_in,
  literalt &carry_out)
{
  carry_out=carry_in;

  Forall_literals(it, bv)
  {
    literalt new_carry=prop.land(carry_out, *it);
    *it=prop.lxor(*it, carry_out);
    carry_out=new_carry;
  }
}

bvt bv_utilst::incrementer(const bvt &bv, literalt carry_in)
{
  bvt result=bv;
  literalt carry_out;
  incrementer(result, carry_in, carry_out);
  return result;
}

bvt bv_utilst::inverted(const bvt &bv)
{
  bvt result=bv;
  Forall_literals(it, result)
    *it=!*it;
  return result;
}

bvt bv_utilst::wallace_tree(const std::vector<bvt> &pps)
{
  PRECONDITION(!pps.empty());

  if(pps.size()==1)
    return pps.front();
  else if(pps.size()==2)
    return add(pps[0], pps[1]);
  else
  {
    std::vector<bvt> new_pps;
    std::size_t no_full_adders=pps.size()/3;

    // add groups of three partial products using CSA
    for(std::size_t i=0; i<no_full_adders; i++)
    {
      const bvt &a=pps[i*3+0],
                &b=pps[i*3+1],
                &c=pps[i*3+2];

      INVARIANT(a.size() == b.size(), "groups should be of equal size");
      INVARIANT(a.size() == c.size(), "groups should be of equal size");

      bvt s(a.size()), t(a.size());

      for(std::size_t bit=0; bit<a.size(); bit++)
      {
        // \todo reformulate using full_adder
        s[bit]=prop.lxor(a[bit], prop.lxor(b[bit], c[bit]));
        t[bit]=(bit==0)?const_literal(false):
               carry(a[bit-1], b[bit-1], c[bit-1]);
      }

      new_pps.push_back(s);
      new_pps.push_back(t);
    }

    // pass onwards up to two remaining partial products
    for(std::size_t i=no_full_adders*3; i<pps.size(); i++)
      new_pps.push_back(pps[i]);

    POSTCONDITION(new_pps.size() < pps.size());
    return wallace_tree(new_pps);
  }
}

bvt bv_utilst::unsigned_multiplier(const bvt &_op0, const bvt &_op1)
{
  #if 1
  bvt op0=_op0, op1=_op1;

  if(is_constant(op1))
    std::swap(op0, op1);

  bvt product;
  product.resize(op0.size());

  for(std::size_t i=0; i<product.size(); i++)
    product[i]=const_literal(false);

  for(std::size_t sum=0; sum<op0.size(); sum++)
    if(op0[sum]!=const_literal(false))
    {
      bvt tmpop;

      tmpop.reserve(op0.size());

      for(std::size_t idx=0; idx<sum; idx++)
        tmpop.push_back(const_literal(false));

      for(std::size_t idx=sum; idx<op0.size(); idx++)
        tmpop.push_back(prop.land(op1[idx-sum], op0[sum]));

      product=add(product, tmpop);
    }

  return product;
  #else
  // Wallace tree multiplier. This is disabled, as runtimes have
  // been observed to go up by 5%-10%, and on some models even by 20%.

  // build the usual quadratic number of partial products

  bvt op0=_op0, op1=_op1;

  if(is_constant(op1))
    std::swap(op0, op1);

  std::vector<bvt> pps;
  pps.reserve(op0.size());

  for(std::size_t bit=0; bit<op0.size(); bit++)
    if(op0[bit]!=const_literal(false))
    {
      bvt pp;

      pp.reserve(op0.size());

      // zeros according to weight
      for(std::size_t idx=0; idx<bit; idx++)
        pp.push_back(const_literal(false));

      for(std::size_t idx=bit; idx<op0.size(); idx++)
        pp.push_back(prop.land(op1[idx-bit], op0[bit]));

      pps.push_back(pp);
    }

  if(pps.empty())
    return zeros(op0.size());
  else
    return wallace_tree(pps);

  #endif
}

bvt bv_utilst::unsigned_multiplier_no_overflow(
  const bvt &op0,
  const bvt &op1)
{
  bvt _op0=op0, _op1=op1;

  PRECONDITION(_op0.size() == _op1.size());

  if(is_constant(_op1))
    _op0.swap(_op1);

  bvt product;
  product.resize(_op0.size());

  for(std::size_t i=0; i<product.size(); i++)
    product[i]=const_literal(false);

  for(std::size_t sum=0; sum<op0.size(); sum++)
    if(op0[sum]!=const_literal(false))
    {
      bvt tmpop;

      tmpop.reserve(product.size());

      for(std::size_t idx=0; idx<sum; idx++)
        tmpop.push_back(const_literal(false));

      for(std::size_t idx=sum; idx<product.size(); idx++)
        tmpop.push_back(prop.land(op1[idx-sum], op0[sum]));

      adder_no_overflow(product, tmpop);

      for(std::size_t idx=op1.size()-sum; idx<op1.size(); idx++)
        prop.l_set_to_false(prop.land(op1[idx], op0[sum]));
    }

  return product;
}

bvt bv_utilst::signed_multiplier(const bvt &op0, const bvt &op1)
{
  if(op0.empty() || op1.empty())
    return bvt();

  literalt sign0=op0[op0.size()-1];
  literalt sign1=op1[op1.size()-1];

  bvt neg0=cond_negate(op0, sign0);
  bvt neg1=cond_negate(op1, sign1);

  bvt result=unsigned_multiplier(neg0, neg1);

  literalt result_sign=prop.lxor(sign0, sign1);

  return cond_negate(result, result_sign);
}

bvt bv_utilst::cond_negate(const bvt &bv, const literalt cond)
{
  bvt neg_bv=negate(bv);

  bvt result;
  result.resize(bv.size());

  for(std::size_t i=0; i<bv.size(); i++)
    result[i]=prop.lselect(cond, neg_bv[i], bv[i]);

  return result;
}

bvt bv_utilst::absolute_value(const bvt &bv)
{
  PRECONDITION(!bv.empty());
  return cond_negate(bv, bv[bv.size()-1]);
}

bvt bv_utilst::cond_negate_no_overflow(const bvt &bv, literalt cond)
{
  prop.l_set_to(
    prop.limplies(cond, !overflow_negate(bv)),
    true);

  return cond_negate(bv, cond);
}

bvt bv_utilst::signed_multiplier_no_overflow(
  const bvt &op0,
  const bvt &op1)
{
  if(op0.empty() || op1.empty())
    return bvt();

  literalt sign0=op0[op0.size()-1];
  literalt sign1=op1[op1.size()-1];

  bvt neg0=cond_negate_no_overflow(op0, sign0);
  bvt neg1=cond_negate_no_overflow(op1, sign1);

  bvt result=unsigned_multiplier_no_overflow(neg0, neg1);

  prop.l_set_to(result[result.size()-1], false);

  literalt result_sign=prop.lxor(sign0, sign1);

  return cond_negate_no_overflow(result, result_sign);
}

bvt bv_utilst::multiplier(
  const bvt &op0,
  const bvt &op1,
  representationt rep)
{
  switch(rep)
  {
  case representationt::SIGNED: return signed_multiplier(op0, op1);
  case representationt::UNSIGNED: return unsigned_multiplier(op0, op1);
  }

  UNREACHABLE;
}

bvt bv_utilst::multiplier_no_overflow(
  const bvt &op0,
  const bvt &op1,
  representationt rep)
{
  switch(rep)
  {
  case representationt::SIGNED:
    return signed_multiplier_no_overflow(op0, op1);
  case representationt::UNSIGNED:
    return unsigned_multiplier_no_overflow(op0, op1);
  }

  UNREACHABLE;
}

void bv_utilst::signed_divider(
  const bvt &op0,
  const bvt &op1,
  bvt &res,
  bvt &rem)
{
  if(op0.empty() || op1.empty())
    return;

  bvt _op0(op0), _op1(op1);

  literalt sign_0=_op0[_op0.size()-1];
  literalt sign_1=_op1[_op1.size()-1];

  bvt neg_0=negate(_op0), neg_1=negate(_op1);

  for(std::size_t i=0; i<_op0.size(); i++)
    _op0[i]=(prop.lselect(sign_0, neg_0[i], _op0[i]));

  for(std::size_t i=0; i<_op1.size(); i++)
    _op1[i]=(prop.lselect(sign_1, neg_1[i], _op1[i]));

  unsigned_divider(_op0, _op1, res, rem);

  bvt neg_res=negate(res), neg_rem=negate(rem);

  literalt result_sign=prop.lxor(sign_0, sign_1);

  for(std::size_t i=0; i<res.size(); i++)
    res[i]=prop.lselect(result_sign, neg_res[i], res[i]);

  for(std::size_t i=0; i<res.size(); i++)
    rem[i]=prop.lselect(sign_0, neg_rem[i], rem[i]);
}

void bv_utilst::divider(
  const bvt &op0,
  const bvt &op1,
  bvt &result,
  bvt &remainer,
  representationt rep)
{
  PRECONDITION(prop.has_set_to());

  switch(rep)
  {
  case representationt::SIGNED:
    signed_divider(op0, op1, result, remainer); break;
  case representationt::UNSIGNED:
    unsigned_divider(op0, op1, result, remainer); break;
  }
}

void bv_utilst::unsigned_divider(
  const bvt &op0,
  const bvt &op1,
  bvt &res,
  bvt &rem)
{
  std::size_t width=op0.size();

  // check if we divide by a power of two
  #if 0
  {
    std::size_t one_count=0, non_const_count=0, one_pos=0;

    for(std::size_t i=0; i<op1.size(); i++)
    {
      literalt l=op1[i];
      if(l.is_true())
      {
        one_count++;
        one_pos=i;
      }
      else if(!l.is_false())
        non_const_count++;
    }

    if(non_const_count==0 && one_count==1 && one_pos!=0)
    {
      // it is a power of two!
      res=shift(op0, LRIGHT, one_pos);

      // remainder is just a mask
      rem=op0;
      for(std::size_t i=one_pos; i<rem.size(); i++)
        rem[i]=const_literal(false);
      return;
    }
  }
  #endif

  // Division by zero test.
  // Note that we produce a non-deterministic result in
  // case of division by zero. SMT-LIB now says the following:
  // bvudiv returns a vector of all 1s if the second operand is 0
  // bvurem returns its first operand if the second operand is 0

  literalt is_not_zero=prop.lor(op1);

  // free variables for result of division

  res.resize(width);
  rem.resize(width);
  for(std::size_t i=0; i<width; i++)
  {
    res[i]=prop.new_variable();
    rem[i]=prop.new_variable();
  }

  // add implications

  bvt product=
    unsigned_multiplier_no_overflow(res, op1);

  // res*op1 + rem = op0

  bvt sum=product;

  adder_no_overflow(sum, rem);

  literalt is_equal=equal(sum, op0);

  prop.l_set_to_true(prop.limplies(is_not_zero, is_equal));

  // op1!=0 => rem < op1

  prop.l_set_to_true(
    prop.limplies(
      is_not_zero, lt_or_le(false, rem, op1, representationt::UNSIGNED)));

  // op1!=0 => res <= op0

  prop.l_set_to_true(
    prop.limplies(
      is_not_zero, lt_or_le(true, res, op0, representationt::UNSIGNED)));
}


#ifdef COMPACT_EQUAL_CONST
// TODO : use for lt_or_le as well

/// The equal_const optimisation will be used on this bit-vector.
/// \par parameters: A bit-vector of a variable that is to be registered.
/// \return None.
void bv_utilst::equal_const_register(const bvt &var)
{
  PRECONDITION(!is_constant(var));
  equal_const_registered.insert(var);
  return;
}


/// The obvious recursive comparison, the interesting thing is that it is cached
/// so the literals are shared between constants.
/// \param Bit:vectors for a variable and a const to compare, note that
/// to avoid significant amounts of copying these are mutable and consumed.
/// \return The literal that is true if and only if all the bits in var and
///   const are equal.
literalt bv_utilst::equal_const_rec(bvt &var, bvt &constant)
{
  std::size_t size = var.size();

  PRECONDITION(size != 0);
  PRECONDITION(size == constant.size());
  PRECONDITION(is_constant(constant));

  if(size == 1)
  {
    literalt comp = prop.lequal(var[size - 1], constant[size - 1]);
    var.pop_back();
    constant.pop_back();
    return comp;
  }
  else
  {
    var_constant_pairt index(var, constant);

    equal_const_cachet::iterator entry = equal_const_cache.find(index);

    if(entry != equal_const_cache.end())
    {
      return entry->second;
    }
    else
    {
      literalt comp = prop.lequal(var[size - 1], constant[size - 1]);
      var.pop_back();
      constant.pop_back();

      literalt rec = equal_const_rec(var, constant);
      literalt compare = prop.land(rec, comp);

      equal_const_cache.insert(
        std::pair<var_constant_pairt, literalt>(index, compare));

      return compare;
    }
  }
}

/// An experimental encoding, aimed primarily at variable position access to
/// constant arrays.  These generate a lot of comparisons of the form var =
/// small_const .  It will introduce some additional literals and for variables
/// that have only a few comparisons with constants this may result in a net
/// increase in formula size.  It is hoped that a 'sufficently advanced
/// preprocessor' will remove these.
/// \param Bit:vectors for a variable and a const to compare.
/// \return The literal that is true if and only if they are equal.
literalt bv_utilst::equal_const(const bvt &var, const bvt &constant)
{
  std::size_t size = constant.size();

  PRECONDITION(var.size() == size);
  PRECONDITION(!is_constant(var));
  PRECONDITION(is_constant(constant));
  PRECONDITION(size >= 2);

  // These get modified : be careful!
  bvt var_upper;
  bvt var_lower;
  bvt constant_upper;
  bvt constant_lower;

  /* Split the constant based on a change in parity
   * This is based on the observation that most constants are small,
   * so combinations of the lower bits are heavily used but the upper
   * bits are almost always either all 0 or all 1.
   */
  literalt top_bit = constant[size - 1];

  std::size_t split = size - 1;
  var_upper.push_back(var[size - 1]);
  constant_upper.push_back(constant[size - 1]);

  for(split = size - 2; split != 0; --split)
  {
    if(constant[split] != top_bit)
    {
      break;
    }
    else
    {
      var_upper.push_back(var[split]);
      constant_upper.push_back(constant[split]);
    }
  }

  for(std::size_t i = 0; i <= split; ++i)
  {
    var_lower.push_back(var[i]);
    constant_lower.push_back(constant[i]);
  }

  // Check we have split the array correctly
  INVARIANT(
    var_upper.size() + var_lower.size() == size,
    "lower size plus upper size should equal the total size");
  INVARIANT(
    constant_upper.size() + constant_lower.size() == size,
    "lower size plus upper size should equal the total size");

  literalt top_comparison = equal_const_rec(var_upper, constant_upper);
  literalt bottom_comparison = equal_const_rec(var_lower, constant_lower);

  return prop.land(top_comparison, bottom_comparison);
}

#endif

/// Bit-blasting ID_equal and use in other encodings.
/// \param op0: Lhs bitvector to compare
/// \param op1: Rhs bitvector to compare
/// \return The literal that is true if and only if they are equal.
literalt bv_utilst::equal(const bvt &op0, const bvt &op1)
{
  PRECONDITION(op0.size() == op1.size());

  #ifdef COMPACT_EQUAL_CONST
  // simplify_expr should put the constant on the right
  // but bit-level simplification may result in the other cases
  if(is_constant(op0) && !is_constant(op1) && op0.size() > 2 &&
      equal_const_registered.find(op1) != equal_const_registered.end())
    return equal_const(op1, op0);
  else if(!is_constant(op0) && is_constant(op1) && op0.size() > 2 &&
      equal_const_registered.find(op0) != equal_const_registered.end())
    return equal_const(op0, op1);
  #endif

  bvt equal_bv;
  equal_bv.resize(op0.size());

  for(std::size_t i=0; i<op0.size(); i++)
    equal_bv[i]=prop.lequal(op0[i], op1[i]);

  return prop.land(equal_bv);
}

/// To provide a bitwise model of < or <=.
/// \par parameters: bvts for each input and whether they are signed and whether
/// a model of < or <= is required.
/// \return A literalt that models the value of the comparison.
/* Some clauses are not needed for correctness but they remove
   models (effectively setting "don't care" bits) and so may be worth
   including.*/
// #define INCLUDE_REDUNDANT_CLAUSES

// Saves space but slows the solver
// There is a variant that uses the xor as an auxiliary that should improve both
// #define COMPACT_LT_OR_LE



literalt bv_utilst::lt_or_le(
  bool or_equal,
  const bvt &bv0,
  const bvt &bv1,
  representationt rep)
{
  PRECONDITION(bv0.size() == bv1.size());

  literalt top0=bv0[bv0.size()-1],
    top1=bv1[bv1.size()-1];

#ifdef COMPACT_LT_OR_LE
  if(prop.has_set_to() && prop.cnf_handled_well())
  {
    bvt compareBelow;   // 1 if a compare is needed below this bit
    literalt result;
    size_t start;
    size_t i;

    compareBelow.resize(bv0.size());
    Forall_literals(it, compareBelow) { (*it) = prop.new_variable(); }
    result = prop.new_variable();

    if(rep==SIGNED)
    {
      INVARIANT(
        bv0.size() >= 2, "signed bitvectors should have at least two bits");
      start = compareBelow.size() - 2;

      literalt firstComp=compareBelow[start];

      // When comparing signs we are comparing the top bit
#ifdef INCLUDE_REDUNDANT_CLAUSES
      prop.l_set_to_true(compareBelow[start + 1])
#endif

      // Four cases...
      prop.lcnf(top0, top1, firstComp);  // + + compare needed
      prop.lcnf(top0, !top1, !result); // + - result false and no compare needed
      prop.lcnf(!top0, top1, result); // - + result true and no compare needed
      prop.lcnf(!top0, !top1, firstComp);  // - - negated compare needed

#ifdef INCLUDE_REDUNDANT_CLAUSES
      prop.lcnf(top0, !top1, !firstComp);
      prop.lcnf(!top0,  top1, !firstComp);
#endif
    }
    else
    {
      // Unsigned is much easier
      start = compareBelow.size() - 1;
      prop.l_set_to_true(compareBelow[start]);
    }

    // Determine the output
    //  \forall i .  cb[i] & -a[i] &  b[i] =>  result
    //  \forall i .  cb[i] &  a[i] & -b[i] => -result
    i = start;
    do
    {
      prop.lcnf(!compareBelow[i],  bv0[i], !bv1[i],  result);
      prop.lcnf(!compareBelow[i], !bv0[i],  bv1[i], !result);
    }
    while(i-- != 0);

    // Chain the comparison bit
    //  \forall i != 0 . cb[i] &  a[i] &  b[i] => cb[i-1]
    //  \forall i != 0 . cb[i] & -a[i] & -b[i] => cb[i-1]
    for(i = start; i > 0; i--)
    {
      prop.lcnf(!compareBelow[i], !bv0[i], !bv1[i], compareBelow[i-1]);
      prop.lcnf(!compareBelow[i],  bv0[i],  bv1[i], compareBelow[i-1]);
    }


#ifdef INCLUDE_REDUNDANT_CLAUSES
    // Optional zeroing of the comparison bit when not needed
    //  \forall i != 0 . -c[i] => -c[i-1]
    //  \forall i != 0 .  c[i] & -a[i] &  b[i] => -c[i-1]
    //  \forall i != 0 .  c[i] &  a[i] & -b[i] => -c[i-1]
    for(i = start; i > 0; i--)
    {
      prop.lcnf(compareBelow[i],                   !compareBelow[i-1]);
      prop.lcnf(!compareBelow[i],  bv0[i], !bv1[i], !compareBelow[i-1]);
      prop.lcnf(!compareBelow[i], !bv0[i],  bv1[i], !compareBelow[i-1]);
    }
#endif

    // The 'base case' of the induction is the case when they are equal
    prop.lcnf(!compareBelow[0], !bv0[0], !bv1[0], (or_equal)?result:!result);
    prop.lcnf(!compareBelow[0],  bv0[0],  bv1[0], (or_equal)?result:!result);

    return result;
  }
  else
#endif
  {
    literalt carry=
      carry_out(bv0, inverted(bv1), const_literal(true));

    literalt result;

    if(rep==representationt::SIGNED)
      result=prop.lxor(prop.lequal(top0, top1), carry);
    else
    {
      INVARIANT(
        rep == representationt::UNSIGNED,
        "representation has either value signed or unsigned");
      result = !carry;
    }

    if(or_equal)
      result=prop.lor(result, equal(bv0, bv1));

    return result;
  }
}

literalt bv_utilst::unsigned_less_than(
  const bvt &op0,
  const bvt &op1)
{
#ifdef COMPACT_LT_OR_LE
  return lt_or_le(false, op0, op1, UNSIGNED);
#else
  // A <= B  iff  there is an overflow on A-B
  return !carry_out(op0, inverted(op1), const_literal(true));
#endif
}

literalt bv_utilst::signed_less_than(
  const bvt &bv0,
  const bvt &bv1)
{
  return lt_or_le(false, bv0, bv1, representationt::SIGNED);
}

literalt bv_utilst::rel(
  const bvt &bv0,
  irep_idt id,
  const bvt &bv1,
  representationt rep)
{
  if(id==ID_equal)
    return equal(bv0, bv1);
  else if(id==ID_notequal)
    return !equal(bv0, bv1);
  else if(id==ID_le)
    return lt_or_le(true, bv0, bv1, rep);
  else if(id==ID_lt)
    return lt_or_le(false, bv0, bv1, rep);
  else if(id==ID_ge)
    return lt_or_le(true, bv1, bv0, rep); // swapped
  else if(id==ID_gt)
    return lt_or_le(false, bv1, bv0, rep); // swapped
  else
    UNREACHABLE;
}

bool bv_utilst::is_constant(const bvt &bv)
{
  forall_literals(it, bv)
    if(!it->is_constant())
      return false;

  return true;
}

void bv_utilst::cond_implies_equal(
  literalt cond,
  const bvt &a,
  const bvt &b)
{
  PRECONDITION(a.size() == b.size());

  if(prop.cnf_handled_well())
  {
    for(std::size_t i=0; i<a.size(); i++)
    {
      prop.lcnf(!cond,  a[i], !b[i]);
      prop.lcnf(!cond, !a[i],  b[i]);
    }
  }
  else
  {
    prop.limplies(cond, equal(a, b));
  }

  return;
}

literalt bv_utilst::verilog_bv_has_x_or_z(const bvt &src)
{
  bvt odd_bits;
  odd_bits.reserve(src.size()/2);

  // check every odd bit
  for(std::size_t i=0; i<src.size(); i++)
  {
    if(i%2!=0)
      odd_bits.push_back(src[i]);
  }

  return prop.lor(odd_bits);
}

bvt bv_utilst::verilog_bv_normal_bits(const bvt &src)
{
  bvt even_bits;
  even_bits.reserve(src.size()/2);

  // get every even bit
  for(std::size_t i=0; i<src.size(); i++)
  {
    if(i%2==0)
      even_bits.push_back(src[i]);
  }

  return even_bits;
}

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>
#include <arith_tools.h>

#include "bv_utils.h"

/*******************************************************************\

Function: bv_utilst::build_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::build_constant(const mp_integer &n, unsigned width)
{
  std::string n_str=integer2binary(n, width);
  bvt result;
  result.resize(width);
  assert(n_str.size()==width);
  for(unsigned i=0; i<width; i++)
    result[i]=const_literal(n_str[width-i-1]=='1');
  return result;
}

/*******************************************************************\

Function: bv_utilst::is_one

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::is_one(const bvt &bv)
{
  assert(!bv.empty());
  bvt tmp;
  tmp=bv;
  tmp.erase(tmp.begin(), tmp.begin()+1);
  return prop.land(is_zero(tmp), bv[0]);
}

/*******************************************************************\

Function: bv_utilst::set_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::set_equal(const bvt &a, const bvt &b)
{
  assert(a.size()==b.size());
  for(unsigned i=0; i<a.size(); i++)
    prop.set_equal(a[i], b[i]);
}

/*******************************************************************\

Function: bv_utilst::extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::extract(const bvt &a, unsigned first, unsigned last) const
{
  // preconditions
  assert(first<a.size());
  assert(last<a.size());
  assert(first<=last);

  bvt result=a;
  result.resize(last+1);
  if(first!=0) result.erase(result.begin(), result.begin()+first);

  assert(result.size()==last-first+1);
  return result;
}

/*******************************************************************\

Function: bv_utilst::concatenate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::concatenate(const bvt &a, const bvt &b) const
{
  bvt result;

  result.resize(a.size()+b.size());

  for(unsigned i=0; i<a.size(); i++)
    result[i]=a[i];

  for(unsigned i=0; i<b.size(); i++)
    result[i+a.size()]=b[i];

  return result;
}

/*******************************************************************\

Function: bv_utilst::select

  Inputs:

 Outputs:

 Purpose: If s is true, selects a otherwise selects b

\*******************************************************************/

bvt bv_utilst::select(literalt s, const bvt &a, const bvt &b)
{
  assert(a.size()==b.size());

  bvt result;

  result.resize(a.size());
  for(unsigned i=0; i<result.size(); i++)
    result[i]=prop.lselect(s, a[i], b[i]);

  return result;
}

/*******************************************************************\

Function: bv_utilst::extension

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::extension(
  const bvt &bv,
  unsigned new_size,
  representationt rep)
{
  unsigned old_size=bv.size();
  bvt result=bv;
  result.resize(new_size);
  
  assert(old_size!=0);

  literalt extend_with=
    (rep==SIGNED && bv.size()!=0)?bv[old_size-1]:
    const_literal(false);

  for(unsigned i=old_size; i<new_size; i++)
    result[i]=extend_with;

  return result;
}

/*******************************************************************\

Function: bv_utilst::carry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::carry(literalt a, literalt b, literalt c)
{
  #if 0

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

  clause.resize(3);
  clause[0]=a;
  clause[1]=b;
  clause[2]=neg(x);
  lcnf(clause);

  clause.resize(4);
  clause[0]=a;
  clause[1]=neg(b);
  clause[2]=c;
  clause[3]=neg(x);
  lcnf(clause);

  clause.resize(4);
  clause[0]=a;
  clause[1]=neg(b);
  clause[2]=neg(c);
  clause[3]=x;
  lcnf(clause);

  clause.resize(4);
  clause[0]=neg(a);
  clause[1]=b;
  clause[2]=c;
  clause[3]=neg(x);
  lcnf(clause);

  clause.resize(4);
  clause[0]=neg(a);
  clause[1]=b;
  clause[2]=neg(c);
  clause[3]=x;
  lcnf(clause);

  clause.resize(3);
  clause[0]=neg(a);
  clause[1]=neg(b);
  clause[2]=x;
  lcnf(clause);

  return x;

  #else

  bvt tmp;

  tmp.push_back(prop.land(a, b));
  tmp.push_back(prop.land(a, c));
  tmp.push_back(prop.land(b, c));

  return prop.lor(tmp);
  #endif
}

/*******************************************************************\

Function: bv_utilst::adder

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::adder(
  bvt &sum,
  const bvt &op,
  literalt carry_in,
  literalt &carry_out)
{
  assert(sum.size()==op.size());

  carry_out=carry_in;

  for(unsigned i=0; i<sum.size(); i++)
  {
    literalt op0_bit=sum[i];
    literalt op1_bit=op[i];

    sum[i]=prop.lxor(
           prop.lxor(op0_bit, op1_bit), carry_out);

    carry_out=carry(op0_bit, op1_bit, carry_out);
  }
}

/*******************************************************************\

Function: bv_utilst::carry_out

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::carry_out(
  const bvt &op0,
  const bvt &op1,
  literalt carry_in)
{
  assert(op0.size()==op1.size());

  literalt carry_out=carry_in;

  for(unsigned i=0; i<op0.size(); i++)
    carry_out=carry(op0[i], op1[i], carry_out);

  return carry_out;
}

/*******************************************************************\

Function: bv_utilst::add_sub_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: bv_utilst::add_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::add_sub(const bvt &op0, const bvt &op1, bool subtract)
{
  assert(op0.size()==op1.size());

  literalt carry_in=const_literal(subtract);
  literalt carry_out;

  bvt result=op0;
  bvt tmp_op1=subtract?inverted(op1):op1;

  adder(result, tmp_op1, carry_in, carry_out);

  return result;
}

/*******************************************************************\

Function: bv_utilst::add_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::add_sub(const bvt &op0, const bvt &op1, literalt subtract)
{
  const bvt op1_sign_applied=
    select(subtract, inverted(op1), op1);

  bvt result=op0;
  literalt carry_out;

  adder(result, op1_sign_applied, subtract, carry_out);

  return result;
}

/*******************************************************************\

Function: bv_utilst::overflow_add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::overflow_add(
  const bvt &op0, const bvt &op1, representationt rep)
{
  if(rep==SIGNED)
  {
    // an overflow occurs if the signs of the two operands are the same
    // and the sign of the sum is the opposite

    literalt old_sign=op0[op0.size()-1];
    literalt sign_the_same=prop.lequal(op0[op0.size()-1], op1[op1.size()-1]);

    literalt carry_out;
    bvt result=add(op0, op1);
    return prop.land(sign_the_same, prop.lxor(result[result.size()-1], old_sign));
  }
  else if(rep==UNSIGNED)
  {
    // overflow is simply carry-out
    return carry_out(op0, op1, const_literal(false));
  }
  else
    assert(false);
}

/*******************************************************************\

Function: bv_utilst::overflow_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::overflow_sub(
  const bvt &op0, const bvt &op1, representationt rep)
{
  // this needs to be fixed!!
  if(rep==SIGNED)
  {
    return overflow_add(op0, negate(op1), SIGNED);
  }
  else if(rep==UNSIGNED)
  {
    // overflow is simply _negated_ carry-out
    return prop.lnot(carry_out(op0, inverted(op1), const_literal(true)));
  }
  else
    assert(false);
}

/*******************************************************************\

Function: bv_utilst::adder_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::adder_no_overflow(
  bvt &sum,
  const bvt &op,
  bool subtract,
  representationt rep)
{
  const bvt tmp_op=subtract?inverted(op):op;

  if(rep==SIGNED)
  {
    // an overflow occurs if the signs of the two operands are the same
    // and the sign of the sum is the opposite

    literalt old_sign=sum[sum.size()-1];
    literalt sign_the_same=prop.lequal(sum[sum.size()-1], tmp_op[tmp_op.size()-1]);

    literalt carry;
    adder(sum, tmp_op, const_literal(subtract), carry);

    // result of addition in sum
    prop.l_set_to_false(
      prop.land(sign_the_same, prop.lxor(sum[sum.size()-1], old_sign)));
  }
  else if(rep==UNSIGNED)
  {
    literalt carry_out;
    adder(sum, tmp_op, const_literal(subtract), carry_out);
    prop.l_set_to(carry_out, subtract);
  }
  else
    assert(false);
}

/*******************************************************************\

Function: bv_utilst::adder_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::adder_no_overflow(bvt &sum, const bvt &op)
{
  literalt carry_out=const_literal(false);

  for(unsigned i=0; i<sum.size(); i++)
  {
    literalt op0_bit=sum[i];

    sum[i]=prop.lxor(
           prop.lxor(op0_bit, op[i]), carry_out);

    carry_out=carry(op0_bit, op[i], carry_out);
  }

  prop.l_set_to_false(carry_out); // enforce no overflow
}

/*******************************************************************\

Function: bv_utilst::shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::shift(const bvt &op, const shiftt s, const bvt &dist)
{
  unsigned d=1, width=op.size();
  bvt result=op;

  for(unsigned stage=0; stage<dist.size(); stage++)
  {
    if(dist[stage]!=const_literal(false))
    {
      bvt tmp=shift(result, s, d);

      for(unsigned i=0; i<width; i++)
        result[i]=prop.lselect(dist[stage], tmp[i], result[i]);
    }

    d=d<<1;
  }

  return result;
}

/*******************************************************************\

Function: bv_utilst::shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::shift(const bvt &src, const shiftt s, unsigned dist)
{
  bvt result;
  result.resize(src.size());

  for(unsigned i=0; i<src.size(); i++)
  {
    literalt l;

    switch(s)
    {
    case LEFT:
      l=(dist<=i?src[i-dist]:const_literal(false));
      break;

    case ARIGHT:
      l=(i+dist<src.size()?src[i+dist]:src[src.size()-1]); // sign bit
      break;

    case LRIGHT:
      l=(i+dist<src.size()?src[i+dist]:const_literal(false));
      break;

    default:
      assert(false);
    }

    result[i]=l;
  }

  return result;
}

/*******************************************************************\

Function: bv_utilst::negate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::negate(const bvt &bv)
{
  bvt result=inverted(bv);
  literalt carry_out;
  incrementer(result, const_literal(true), carry_out);
  return result;
}

/*******************************************************************\

Function: bv_utilst::negate_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::negate_no_overflow(const bvt &bv)
{
  prop.l_set_to(overflow_negate(bv), false);
  return negate(bv);
}

/*******************************************************************\

Function: bv_utilst::overflow_negate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::overflow_negate(const bvt &bv)
{
  // a overflow on unary- can only happen with the smallest
  // representable number 100....0

  bvt zeros;

  for(unsigned i=0; i<bv.size()-1; i++)
    zeros.push_back(bv[i]);

  return prop.land(bv[bv.size()-1], prop.lnot(prop.lor(zeros)));
}

/*******************************************************************\

Function: bv_utilst::incrementer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: bv_utilst::incrementer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::incrementer(const bvt &bv, literalt carry_in)
{
  bvt result=bv;
  literalt carry_out;
  incrementer(result, carry_in, carry_out);
  return result;
}

/*******************************************************************\

Function: bv_utilst::invert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::inverted(const bvt &bv)
{
  bvt result=bv;
  Forall_literals(it, result)
    *it=prop.lnot(*it);
  return result;
}

/*******************************************************************\

Function: bv_utilst::unsigned_multiplier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::unsigned_multiplier(const bvt &_op0, const bvt &_op1)
{
  bvt op0=_op0, op1=_op1;

  if(is_constant(op1))
    std::swap(op0, op1);

  bvt product;
  product.resize(op0.size());

  for(unsigned i=0; i<product.size(); i++)
    product[i]=const_literal(false);

  for(unsigned sum=0; sum<op0.size(); sum++)
    if(op0[sum]!=const_literal(false))
    {
      bvt tmpop;

      tmpop.reserve(op0.size());

      for(unsigned idx=0; idx<sum; idx++)
        tmpop.push_back(const_literal(false));

      for(unsigned idx=sum; idx<op0.size(); idx++)
        tmpop.push_back(prop.land(op1[idx-sum], op0[sum]));

      product=add(product, tmpop);
    }

  return product;
}

/*******************************************************************\

Function: bv_utilst::unsigned_multiplier_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::unsigned_multiplier_no_overflow(
  const bvt &op0,
  const bvt &op1)
{
  bvt _op0=op0, _op1=op1;

  if(is_constant(_op1))
    _op0.swap(_op1);

  assert(_op0.size()==_op1.size());

  bvt product;
  product.resize(_op0.size());

  for(unsigned i=0; i<product.size(); i++)
    product[i]=const_literal(false);

  for(unsigned sum=0; sum<op0.size(); sum++)
    if(op0[sum]!=const_literal(false))
    {
      bvt tmpop;

      tmpop.reserve(product.size());

      for(unsigned idx=0; idx<sum; idx++)
        tmpop.push_back(const_literal(false));

      for(unsigned idx=sum; idx<product.size(); idx++)
        tmpop.push_back(prop.land(op1[idx-sum], op0[sum]));

      adder_no_overflow(product, tmpop);

      for(unsigned idx=op1.size()-sum; idx<op1.size(); idx++)
        prop.l_set_to_false(prop.land(op1[idx], op0[sum]));
    }

  return product;
}

/*******************************************************************\

Function: bv_utilst::signed_multiplier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::signed_multiplier(const bvt &op0, const bvt &op1)
{
  if(op0.size()==0 || op1.size()==0) return bvt();

  literalt sign0=op0[op0.size()-1];
  literalt sign1=op1[op1.size()-1];

  bvt neg0=cond_negate(op0, sign0);
  bvt neg1=cond_negate(op1, sign1);

  bvt result=unsigned_multiplier(neg0, neg1);

  literalt result_sign=prop.lxor(sign0, sign1);

  return cond_negate(result, result_sign);
}

/*******************************************************************\

Function: bv_utilst::cond_negate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::cond_negate(const bvt &bv, const literalt cond)
{
  bvt neg_bv=negate(bv);

  bvt result;
  result.resize(bv.size());

  for(unsigned i=0; i<bv.size(); i++)
    result[i]=prop.lselect(cond, neg_bv[i], bv[i]);

  return result;
}

/*******************************************************************\

Function: bv_utilst::absolute_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::absolute_value(const bvt &bv)
{
  assert(!bv.empty());
  return cond_negate(bv, bv[bv.size()-1]);
}

/*******************************************************************\

Function: bv_utilst::cond_negate_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::cond_negate_no_overflow(const bvt &bv, literalt cond)
{
  prop.l_set_to(
    prop.limplies(cond, prop.lnot(overflow_negate(bv))),
    true);

  return cond_negate(bv, cond);
}

/*******************************************************************\

Function: bv_utilst::signed_multiplier_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::signed_multiplier_no_overflow(
  const bvt &op0,
  const bvt &op1)
{
  if(op0.size()==0 || op1.size()==0) return bvt();

  literalt sign0=op0[op0.size()-1];
  literalt sign1=op1[op1.size()-1];

  bvt neg0=cond_negate_no_overflow(op0, sign0);
  bvt neg1=cond_negate_no_overflow(op1, sign1);

  bvt result=unsigned_multiplier_no_overflow(neg0, neg1);

  prop.l_set_to(result[result.size()-1], false);

  literalt result_sign=prop.lxor(sign0, sign1);

  return cond_negate_no_overflow(result, result_sign);
}

/*******************************************************************\

Function: bv_utilst::multiplier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::multiplier(
  const bvt &op0,
  const bvt &op1,
  representationt rep)
{
  switch(rep)
  {
  case SIGNED: return signed_multiplier(op0, op1);
  case UNSIGNED: return unsigned_multiplier(op0, op1);
  default: assert(false);
  }
}

/*******************************************************************\

Function: bv_utilst::multiplier_no_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt bv_utilst::multiplier_no_overflow(
  const bvt &op0,
  const bvt &op1,
  representationt rep)
{
  switch(rep)
  {
  case SIGNED: return signed_multiplier_no_overflow(op0, op1);
  case UNSIGNED: return unsigned_multiplier_no_overflow(op0, op1);
  default: assert(false);
  }
}

/*******************************************************************\

Function: bv_utilst::signed_divider

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::signed_divider(
  const bvt &op0,
  const bvt &op1,
  bvt &res,
  bvt &rem)
{
  if(op0.size()==0 || op1.size()==0) return;

  bvt _op0(op0), _op1(op1);

  literalt sign_0=_op0[_op0.size()-1];
  literalt sign_1=_op1[_op1.size()-1];

  bvt neg_0=negate(_op0), neg_1=negate(_op1);

  for(unsigned i=0; i<_op0.size(); i++)
    _op0[i]=(prop.lselect(sign_0, neg_0[i], _op0[i]));

  for(unsigned i=0; i<_op1.size(); i++)
    _op1[i]=(prop.lselect(sign_1, neg_1[i], _op1[i]));

  unsigned_divider(_op0, _op1, res, rem);

  bvt neg_res=negate(res), neg_rem=negate(rem);

  literalt result_sign=prop.lxor(sign_0, sign_1);

  for(unsigned i=0; i<res.size(); i++)
    res[i]=prop.lselect(result_sign, neg_res[i], res[i]);

  for(unsigned i=0; i<res.size(); i++)
    rem[i]=prop.lselect(sign_0, neg_rem[i], rem[i]);
}

/*******************************************************************\

Function: bv_utilst::divider

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::divider(
  const bvt &op0,
  const bvt &op1,
  bvt &result,
  bvt &remainer,
  representationt rep)
{
  assert(prop.has_set_to());

  switch(rep)
  {
  case SIGNED: signed_divider(op0, op1, result, remainer); break;
  case UNSIGNED: unsigned_divider(op0, op1, result, remainer); break;
  default: assert(false);
  }
}

/*******************************************************************\

Function: bv_utilst::unsigned_divider

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::unsigned_divider(
  const bvt &op0,
  const bvt &op1,
  bvt &res,
  bvt &rem)
{
  unsigned width=op0.size();
  
  // check if we divide by a power of two
  #if 0
  {
    unsigned one_count=0, non_const_count=0, one_pos=0;
    
    for(unsigned i=0; i<op1.size(); i++)
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
      for(unsigned i=one_pos; i<rem.size(); i++)
        rem[i]=const_literal(false);
      return;
    }
  }
  #endif

  // division by zero test

  literalt is_not_zero=prop.lor(op1);

  // free variables for result of division

  res.resize(width);
  rem.resize(width);
  for(unsigned i=0; i<width; i++)
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
    prop.limplies(is_not_zero, lt_or_le(false, rem, op1, UNSIGNED)));

  // op1!=0 => res <= op0

  prop.l_set_to_true(
    prop.limplies(is_not_zero, lt_or_le(true, res, op0, UNSIGNED)));
}

/*******************************************************************\

Function: bv_utilst::equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::equal(const bvt &op0, const bvt &op1)
{
  assert(op0.size()==op1.size());

  bvt equal_bv;
  equal_bv.resize(op0.size());

  for(unsigned i=0; i<op0.size(); i++)
    equal_bv[i]=prop.lequal(op0[i], op1[i]);

  return prop.land(equal_bv);
}

/*******************************************************************\

Function: bv_utilst::lt_or_le

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::lt_or_le(
  bool or_equal,
  const bvt &bv0,
  const bvt &bv1,
  representationt rep)
{
  literalt top0=bv0[bv0.size()-1],
           top1=bv1[bv1.size()-1];

  literalt carry=
    carry_out(bv0, inverted(bv1), const_literal(true));

  literalt result;

  if(rep==SIGNED)
    result=prop.lxor(prop.lequal(top0, top1), carry);
  else if(rep==UNSIGNED)
    result=prop.lnot(carry);
  else
    assert(false);

  if(or_equal)
    result=prop.lor(result, equal(bv0, bv1));

  return result;
}

/*******************************************************************\

Function: bv_utilst::unsigned_less_than

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::unsigned_less_than(
  const bvt &op0,
  const bvt &op1)
{
  // A <= B  iff  there is an overflow on A-B

  return prop.lnot(
    carry_out(op0, inverted(op1), const_literal(true)));
}

/*******************************************************************\

Function: bv_utilst::signed_less_than

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_utilst::signed_less_than(
  const bvt &bv0,
  const bvt &bv1)
{
  return lt_or_le(false, bv0, bv1, SIGNED);
}

/*******************************************************************\

Function: bv_utilst::is_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bv_utilst::is_constant(const bvt &bv)
{
  forall_literals(it, bv)
    if(!it->is_constant())
      return false;

  return true;
}

/*******************************************************************\

Function: bv_utilst::cond_implies_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_utilst::cond_implies_equal(
  literalt cond,
  const bvt &a,
  const bvt &b)
{
  assert(a.size()==b.size());

  for(unsigned i=0; i<a.size(); i++)
  {
    bvt clause1;

    clause1.push_back(prop.lnot(cond));
    clause1.push_back(a[i]);
    clause1.push_back(prop.lnot(b[i]));

    prop.lcnf(clause1);

    bvt clause2;

    clause2.push_back(prop.lnot(cond));
    clause2.push_back(prop.lnot(a[i]));
    clause2.push_back(b[i]);

    prop.lcnf(clause2);
  }
}

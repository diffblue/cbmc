/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_utils.h"

#include <util/arith_tools.h>

#include <climits>
#include <iostream>
#include <list>
#include <map>
#include <utility>

static std::string beautify(const bvt &bv)
{
  for(const auto &v : bv)
  {
    if(!v.is_constant())
    {
      std::ostringstream oss;
      oss << bv;
      return oss.str();
    }
  }

  std::string result;
  std::size_t number = 0;
  for(std::size_t i = 0; i < bv.size(); ++i)
  {
    if(result.size() % 5 == 4)
      result = std::string(" ") + result;
    result = std::string(bv[i].is_false() ? "0" : "1") + result;

    if(bv[i].is_true())
      number += 1 << i;
  }

  return result + " (" + std::to_string(number) + ")";
}

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

bvt bv_utilst::concatenate(const bvt &a, const bvt &b)
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

    // Register XOR constraint: sum = a XOR b XOR carry_in
    return sum;
  }
  else // NOLINT(readability/braces)
  #endif // OPTIMAL_FULL_ADDER
  {
    // trivial encoding
    carry_out=carry(a, b, carry_in);
    literalt sum = prop.lxor(prop.lxor(a, b), carry_in);
    // Register XOR constraint: sum = a XOR b XOR carry_in
    return sum;
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

std::pair<bvt, literalt> bv_utilst::optimized_ripple_carry_adder(
  const bvt &op0,
  const bvt &op1,
  literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());

  std::pair<bvt, literalt> result{bvt{}, carry_in};
  result.first.reserve(op0.size());
  literalt &carry_out = result.second;

  for(std::size_t i = 0; i < op0.size(); i++)
  {
    result.first.push_back(full_adder(op0[i], op1[i], carry_out, carry_out));
  }

  return result;
}

std::pair<bvt, literalt> bv_utilst::carry_lookahead_adder(
  const bvt &op0,
  const bvt &op1,
  literalt carry_in)
{
  PRECONDITION(prop.cnf_handled_well());
  PRECONDITION(op0.size() == op1.size());

  std::pair<bvt, literalt> result{op0, literalt{}};
  bvt &sum = result.first;

  bvt constants;
  constants.reserve(2);
  if(op0[0].is_constant())
    constants.push_back(op0[0]);
  if(op1[0].is_constant())
    constants.push_back(op1[0]);
  else
    sum[0] = op1[0];
  if(constants.size() == 2)
    sum[0] = constants[0] == constants[1] ? carry_in : !carry_in;
  else if(constants.size() == 1 && carry_in.is_constant())
  {
    if(constants[0] != carry_in)
      sum[0].invert();
  }
  else
  {
    sum[0] = prop.new_variable();
    prop.lcnf({sum[0], op0[0], op1[0], !carry_in});
    prop.lcnf({sum[0], op0[0], !op1[0], carry_in});
    prop.lcnf({sum[0], !op0[0], op1[0], carry_in});
    prop.lcnf({sum[0], !op0[0], !op1[0], !carry_in});
    prop.lcnf({!sum[0], op0[0], op1[0], carry_in});
    prop.lcnf({!sum[0], op0[0], !op1[0], !carry_in});
    prop.lcnf({!sum[0], !op0[0], op1[0], !carry_in});
    prop.lcnf({!sum[0], !op0[0], !op1[0], carry_in});
  }

  for(std::size_t i = 1; i < sum.size(); i++)
  {
    sum[i] = prop.new_variable();

    prop.lcnf({sum[i], op0[i], op1[i], !op0[i - 1], !op1[i - 1]});
    prop.lcnf({sum[i], op0[i], op1[i], sum[i - 1], !op0[i - 1]});
    prop.lcnf({sum[i], op0[i], op1[i], sum[i - 1], !op1[i - 1]});

    prop.lcnf({sum[i], op0[i], !op1[i], op0[i - 1], op1[i - 1]});
    prop.lcnf({sum[i], op0[i], !op1[i], !sum[i - 1], op0[i - 1]});
    prop.lcnf({sum[i], op0[i], !op1[i], !sum[i - 1], op1[i - 1]});

    prop.lcnf({sum[i], !op0[i], op1[i], op0[i - 1], op1[i - 1]});
    prop.lcnf({sum[i], !op0[i], op1[i], !sum[i - 1], op0[i - 1]});
    prop.lcnf({sum[i], !op0[i], op1[i], !sum[i - 1], op1[i - 1]});

    prop.lcnf({sum[i], !op0[i], !op1[i], !op0[i - 1], !op1[i - 1]});
    prop.lcnf({sum[i], !op0[i], !op1[i], sum[i - 1], !op0[i - 1]});
    prop.lcnf({sum[i], !op0[i], !op1[i], sum[i - 1], !op1[i - 1]});

    prop.lcnf({!sum[i], op0[i], op1[i], op0[i - 1], op1[i - 1]});
    prop.lcnf({!sum[i], op0[i], op1[i], !sum[i - 1], op0[i - 1]});
    prop.lcnf({!sum[i], op0[i], op1[i], !sum[i - 1], op1[i - 1]});

    prop.lcnf({!sum[i], op0[i], !op1[i], !op0[i - 1], !op1[i - 1]});
    prop.lcnf({!sum[i], op0[i], !op1[i], sum[i - 1], !op0[i - 1]});
    prop.lcnf({!sum[i], op0[i], !op1[i], sum[i - 1], !op1[i - 1]});

    prop.lcnf({!sum[i], !op0[i], op1[i], !op0[i - 1], !op1[i - 1]});
    prop.lcnf({!sum[i], !op0[i], op1[i], sum[i - 1], !op0[i - 1]});
    prop.lcnf({!sum[i], !op0[i], op1[i], sum[i - 1], !op1[i - 1]});

    prop.lcnf({!sum[i], !op0[i], !op1[i], op0[i - 1], op1[i - 1]});
    prop.lcnf({!sum[i], !op0[i], !op1[i], !sum[i - 1], op0[i - 1]});
    prop.lcnf({!sum[i], !op0[i], !op1[i], !sum[i - 1], op1[i - 1]});
  }

  result.second = prop.lor(
    prop.land(op0.back(), op1.back()),
    prop.land(!sum.back(), prop.lor(op0.back(), op1.back())));

  return result;
}

std::pair<bvt, literalt> bv_utilst::simple_ripple_carry_adder(
  const bvt &op0,
  const bvt &op1,
  literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());

  std::pair<bvt, literalt> result;
  result.first.reserve(op0.size());
  bvt carries;
  carries.reserve(op0.size() + 1);

  carries.push_back(carry_in);

  for(std::size_t i = 0; i < op0.size(); i++)
  {
    literalt c_i_minus_1 = carries.back();
#if 1
    carries.push_back(prop.lor(
      {prop.land(op0[i], op1[i]),
       prop.land(op0[i], c_i_minus_1),
       prop.land(op1[i], c_i_minus_1)}));
    result.first.push_back(prop.lxor({op0[i], op1[i], c_i_minus_1}));
#else
    // Area optimized low power arithmetic and logic unit. Rani et al. 2011
    literalt x = !prop.lxor(op0[i], op1[i]);
    result.first.push_back(!prop.lxor(x, c_i_minus_1));
    carries.push_back(prop.lselect(x, op0[i], c_i_minus_1));
#endif
  }

  result.second = carries.back();
  return result;
}

std::pair<bvt, literalt> bv_utilst::carry_lookahead_4_bit_adder(
  const bvt &op0,
  const bvt &op1,
  literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());

  std::pair<bvt, literalt> result;
  result.first.reserve(op0.size());
  bvt carries;
  carries.reserve(op0.size());
  bvt generate;
  generate.reserve(op0.size());
  bvt propagate;
  propagate.reserve(op0.size());

  bvt group_var1, group_var2;
  group_var1.reserve(3);
  group_var2.reserve(2);
  literalt group_var3;

  carries.push_back(carry_in);

  for(std::size_t i = 0; i < op0.size(); i++)
  {
    literalt c_i_minus_1 = carries.back();
    generate.push_back(prop.land(op0[i], op1[i]));
    propagate.push_back(prop.lor(op0[i], op1[i])); // could also use lxor

    result.first.push_back(prop.lxor({op0[i], op1[i], c_i_minus_1}));

    switch(i % 4)
    {
    case 0:
      group_var1.clear();
      group_var1.push_back(prop.land(propagate.back(), c_i_minus_1));
      carries.push_back(prop.lor(generate.back(), group_var1[0]));
      break;
    case 1:
      group_var1.push_back(prop.land(group_var1[0], propagate.back()));
      group_var2.clear();
      group_var2.push_back(prop.land(generate.rbegin()[1], propagate.back()));
      carries.push_back(
        prop.lor({generate.back(), group_var2[0], group_var1[1]}));
      break;
    case 2:
      group_var1.push_back(prop.land(group_var1[1], propagate.back()));
      group_var2.push_back(prop.land(group_var2[0], propagate.back()));
      group_var3 = prop.land(generate.rbegin()[1], propagate.back());
      carries.push_back(
        prop.lor({generate.back(), group_var3, group_var2[1], group_var1[2]}));
      break;
    case 3:
      carries.push_back(prop.lor(
        generate.back(),
        prop.land(
          prop.lor(
            {generate.rbegin()[1], group_var3, group_var2[1], group_var1[2]}),
          propagate.back())));
      break;
    }
  }

  result.second = carries.back();
  return result;
}

std::pair<bvt, literalt>
bv_utilst::kogge_stone_adder(const bvt &op0, const bvt &op1, literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());
  PRECONDITION(!op0.empty());

  std::map<std::pair<std::size_t, std::size_t>, literalt> generate, propagate;

  for(std::size_t i = 0; i < op0.size(); i++)
  {
    generate.emplace(std::make_pair(i, i), prop.land(op0[i], op1[i]));
    propagate.emplace(std::make_pair(i, i), prop.lxor(op0[i], op1[i]));
  }

  std::size_t L = address_bits(op0.size());

  for(std::size_t llevel = 1; llevel <= L + 1; ++llevel)
  {
    std::size_t u = 1ll << llevel;
    std::size_t v = u >> 1;

    {
      // with i = v - 1:
      // GP_{i : i - u  + 1} = GP_{i : i - v + 1} \circ GP_{i - v : i - u + 1}
      // where all indices are set to -1 if less than that

      auto g__i__i_v_1 = generate.find({v - 1, 0});
      CHECK_RETURN(g__i__i_v_1 != generate.end());
      auto p__i__i_v_1 = propagate.find({v - 1, 0});
      CHECK_RETURN(p__i__i_v_1 != propagate.end());

      generate.emplace(
        std::make_pair(v - 1, SIZE_MAX),
        prop.lor(
          g__i__i_v_1->second, prop.land(p__i__i_v_1->second, carry_in)));
      propagate.emplace(std::make_pair(v - 1, SIZE_MAX), const_literal(false));
    }
    for(std::size_t i = v; i < op0.size() - 1; ++i)
    {
      // GP_{i : i - u  + 1} = GP_{i : i - v + 1} \circ GP_{i - v : i - u + 1}
      // where all indices are set to -1 if less than that
      auto lb = i + 1 < u ? SIZE_MAX : i + 1 - u;

      auto g__i__i_v_1 = generate.find({i, i - v + 1});
      CHECK_RETURN(g__i__i_v_1 != generate.end());
      auto g__i_v__i_u_1 = generate.find({i - v, lb});
      CHECK_RETURN(g__i_v__i_u_1 != generate.end());
      auto p__i__i_v_1 = propagate.find({i, i - v + 1});
      CHECK_RETURN(p__i__i_v_1 != propagate.end());
      auto p__i_v__i_u_1 = propagate.find({i - v, lb});
      CHECK_RETURN(p__i_v__i_u_1 != propagate.end());

      generate.emplace(
        std::make_pair(i, lb),
        prop.lor(
          g__i__i_v_1->second,
          prop.land(p__i__i_v_1->second, g__i_v__i_u_1->second)));
      propagate.emplace(
        std::make_pair(i, lb),
        prop.land(p__i__i_v_1->second, p__i_v__i_u_1->second));
    }
    if(llevel <= L)
    {
      auto i = op0.size() - 1;
      // GP_{i : i - u  + 1} = GP_{i : i - v + 1} \circ GP_{i - v : i - u + 1}
      // where all indices are set to -1 if less than that
      auto lb = i + 1 < u ? SIZE_MAX : i + 1 - u;

      auto g__i__i_v_1 = generate.find({i, i - v + 1});
      CHECK_RETURN(g__i__i_v_1 != generate.end());
      auto g__i_v__i_u_1 = generate.find({i - v, lb});
      CHECK_RETURN(g__i_v__i_u_1 != generate.end());
      auto p__i__i_v_1 = propagate.find({i, i - v + 1});
      CHECK_RETURN(p__i__i_v_1 != propagate.end());
      auto p__i_v__i_u_1 = propagate.find({i - v, lb});
      CHECK_RETURN(p__i_v__i_u_1 != propagate.end());

      generate.emplace(
        std::make_pair(i, lb),
        prop.lor(
          g__i__i_v_1->second,
          prop.land(p__i__i_v_1->second, g__i_v__i_u_1->second)));
      propagate.emplace(
        std::make_pair(i, lb),
        prop.land(p__i__i_v_1->second, p__i_v__i_u_1->second));
    }
  }

  std::pair<bvt, literalt> result;
  result.first.reserve(op0.size());

  result.first.push_back(prop.lxor(propagate.at({0, 0}), carry_in));
  for(std::size_t i = 1; i < op0.size(); i++)
  {
    result.first.push_back(
      prop.lxor(propagate.at({i, i}), generate.at({i - 1, SIZE_MAX})));
  }

  // carry-out
  result.second = generate.at({op0.size() - 1, SIZE_MAX});
  return result;
}

std::pair<bvt, literalt>
bv_utilst::brent_kung_adder(const bvt &op0, const bvt &op1, literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());
  PRECONDITION(!op0.empty());

  std::map<std::pair<std::size_t, std::size_t>, literalt> generate, propagate;

  for(std::size_t i = 0; i < op0.size(); i++)
  {
    generate.emplace(std::make_pair(i, i), prop.land(op0[i], op1[i]));
    propagate.emplace(std::make_pair(i, i), prop.lxor(op0[i], op1[i]));
  }

  std::size_t L = address_bits(op0.size());

  for(std::size_t llevel = 1; llevel <= L; ++llevel)
  {
    std::size_t u = 1ll << llevel;
    std::size_t v = u >> 1;

    if(llevel == 1)
    {
      // with i = u - 2:
      // GP_{i : i - u  + 1} = GP_{i : i - v + 1} \circ GP_{i - v : i - u + 1}
      // where all indices are set to -1 if less than that
      // auto i = u - 2;

      auto g__i__i_v_1 = generate.find({u - 2, v - 1});
      CHECK_RETURN(g__i__i_v_1 != generate.end());
      auto p__i__i_v_1 = propagate.find({u - 2, v - 1});
      CHECK_RETURN(p__i__i_v_1 != propagate.end());

      generate.emplace(
        std::make_pair(u - 2, SIZE_MAX),
        prop.lor(g__i__i_v_1->second, prop.land(p__i__i_v_1->second, carry_in)));
    }
    for(std::size_t i = (llevel == 1 ? 2 * u - 2 : u - 2); i < op0.size() - 1;
        i += u)
    {
      // GP_{i : i - u  + 1} = GP_{i : i - v + 1} \circ GP_{i - v : i - u + 1}
      // where all indices are set to -1 if less than that
      auto lb = i + 1 < u ? SIZE_MAX : i + 1 - u;

      auto g__i__i_v_1 = generate.find({i, i - v + 1});
      CHECK_RETURN(g__i__i_v_1 != generate.end());
      auto g__i_v__i_u_1 = generate.find({i - v, lb});
      CHECK_RETURN(g__i_v__i_u_1 != generate.end());
      auto p__i__i_v_1 = propagate.find({i, i - v + 1});
      CHECK_RETURN(p__i__i_v_1 != propagate.end());

      generate.emplace(
        std::make_pair(i, lb),
        prop.lor(g__i__i_v_1->second, prop.land(p__i__i_v_1->second, g__i_v__i_u_1->second)));
      if(lb != SIZE_MAX)
      {
        auto p__i_v__i_u_1 = propagate.find({i - v, lb});
        CHECK_RETURN(p__i_v__i_u_1 != propagate.end());
        propagate.emplace(
          std::make_pair(i, lb),
          prop.land(p__i__i_v_1->second, p__i_v__i_u_1->second));
      }
    }
  }

  for(std::size_t llevel = L - 1; llevel >= 1; --llevel)
  {
    std::size_t u = 1ll << llevel;
    std::size_t v = u >> 1;

    for(std::size_t i = u + v - 2; i < op0.size(); i += u)
    {
      // GP_{i : -1} = GP_{i : i - v + 1} \circ GP_{i - v : -1}
      // where all indices are set to -1 if less than that

      auto g__i__i_v_1 = generate.find({i, i - v + 1});
      CHECK_RETURN(g__i__i_v_1 != generate.end());
      auto g__i_v___1 = generate.find({i - v, SIZE_MAX});
      CHECK_RETURN(g__i_v___1 != generate.end());
      auto p__i__i_v_1 = propagate.find({i, i - v + 1});
      CHECK_RETURN(p__i__i_v_1 != propagate.end());

      generate.emplace(
        std::make_pair(i, SIZE_MAX),
        prop.lor(g__i__i_v_1->second, prop.land(p__i__i_v_1->second, g__i_v___1->second)));
    }
  }

  std::pair<bvt, literalt> result;
  result.first.reserve(op0.size());

  result.first.push_back(prop.lxor(propagate.at({0, 0}), carry_in));
  for(std::size_t i = 1; i < op0.size(); i++)
  {
    result.first.push_back(
      prop.lxor(propagate.at({i, i}), generate.at({i - 1, SIZE_MAX})));
  }

  // carry-out
  result.second = generate.at({op0.size() - 1, SIZE_MAX});
  return result;
}

std::pair<bvt, literalt>
bv_utilst::sklansky_adder(const bvt &op0, const bvt &op1, literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());
  PRECONDITION(!op0.empty());

  std::map<std::pair<std::size_t, std::size_t>, literalt> generate, propagate;

  for(std::size_t i = 0; i < op0.size(); i++)
  {
    generate.emplace(std::make_pair(i, i), prop.land(op0[i], op1[i]));
    propagate.emplace(std::make_pair(i, i), prop.lxor(op0[i], op1[i]));
  }

  std::size_t L = address_bits(op0.size());

  for(std::size_t llevel = 1; llevel <= L; ++llevel)
  {
    std::size_t u = 1ll << llevel;
    std::size_t v = u >> 1;

    if(llevel == 1)
    {
      // with i = u - 2:
      // GP_{i : i - u  + 1} = GP_{i : i - v + 1} \circ GP_{i - v : i - u + 1}
      // where all indices are set to -1 if less than that

      auto g__i__i_v_1 = generate.find({u - 2, v - 1});
      CHECK_RETURN(g__i__i_v_1 != generate.end());
      auto p__i__i_v_1 = propagate.find({u - 2, v - 1});
      CHECK_RETURN(p__i__i_v_1 != propagate.end());

      generate.emplace(
        std::make_pair(u - 2, SIZE_MAX),
        prop.lor(
          g__i__i_v_1->second, prop.land(p__i__i_v_1->second, carry_in)));
    }
    for(std::size_t i = (llevel == 1 ? 2 * u - 2 : u - 2); i < op0.size() - 1;
        i += u)
    {
      for(std::size_t j = i; j > i - v; --j)
      {
        // GP_{i : i - u  + 1} = GP_{i : i - v + 1} \circ GP_{i - v : i - u + 1}
        // where all indices are set to -1 if less than that
        auto lb = i + 1 < u ? SIZE_MAX : i + 1 - u;

        auto g__j__i_v_1 = generate.find({j, i - v + 1});
        CHECK_RETURN(g__j__i_v_1 != generate.end());
        auto g__i_v__i_u_1 = generate.find({i - v, lb});
        CHECK_RETURN(g__i_v__i_u_1 != generate.end());
        auto p__j__i_v_1 = propagate.find({j, i - v + 1});
        CHECK_RETURN(p__j__i_v_1 != propagate.end());

        generate.emplace(
          std::make_pair(j, lb),
          prop.lor(
            g__j__i_v_1->second,
            prop.land(p__j__i_v_1->second, g__i_v__i_u_1->second)));
        if(lb != SIZE_MAX)
        {
          auto p__i_v__i_u_1 = propagate.find({i - v, lb});
          CHECK_RETURN(p__i_v__i_u_1 != propagate.end());
          propagate.emplace(
            std::make_pair(j, lb),
            prop.land(p__j__i_v_1->second, p__i_v__i_u_1->second));
        }
      }
    }
  }

  std::pair<bvt, literalt> result;
  result.first.reserve(op0.size());

  result.first.push_back(prop.lxor(propagate.at({0, 0}), carry_in));
  for(std::size_t i = 1; i < op0.size(); i++)
  {
    result.first.push_back(
      prop.lxor(propagate.at({i, i}), generate.at({i - 1, SIZE_MAX})));
  }

  // carry-out
  generate.emplace(
    std::make_pair(op0.size() - 1, SIZE_MAX),
    prop.lor(
      generate.at({op0.size() - 1, op0.size() - 1}),
      prop.land(
        propagate.at({op0.size() - 1, op0.size() - 1}),
        generate.at({op0.size() - 2, SIZE_MAX}))));
  result.second = generate.at({op0.size() - 1, SIZE_MAX});
  return result;
}



std::pair<bvt, literalt>
bv_utilst::ladner_fischer_adder(
  const bvt &op0, const bvt &op1, literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());
  PRECONDITION(!op0.empty());

  std::size_t n = op0.size();
  // Per-bit generate and propagate
  std::vector<literalt> g(n), p(n);
  for(std::size_t i = 0; i < n; i++)
  {
    g[i] = prop.land(op0[i], op1[i]);
    p[i] = prop.lxor(op0[i], op1[i]);
  }

  // Ladner-Fischer prefix tree: at each level, merge adjacent pairs
  // but only update even-indexed positions. Then propagate to odd.
  // This is like Sklansky but processes positions in a specific order
  // to minimize fan-out.
  std::size_t L = address_bits(n);
  for(std::size_t lev = 0; lev < L; lev++)
  {
    std::size_t stride = std::size_t{1} << (lev + 1);
    std::size_t half = stride >> 1;
    // Merge: position i merges with position i - half
    for(std::size_t i = stride - 1; i < n; i += stride)
    {
      std::size_t j = i - half;
      // G[i] = g[i] OR (p[i] AND g[j])
      // P[i] = p[i] AND p[j]
      g[i] = prop.lor(g[i], prop.land(p[i], g[j]));
      p[i] = prop.land(p[i], p[j]);
    }
  }
  // Reverse sweep: fill in positions that weren't computed
  for(std::size_t lev = L - 1; lev >= 1; lev--)
  {
    std::size_t stride = std::size_t{1} << lev;
    std::size_t half = stride >> 1;
    for(std::size_t i = stride + half - 1; i < n; i += stride)
    {
      std::size_t j = i - half;
      g[i] = prop.lor(g[i], prop.land(p[i], g[j]));
      // p[i] not needed after this
    }
  }

  // Compute carries and sums
  std::pair<bvt, literalt> result;
  result.first.reserve(n);
  // carry[0] = carry_in, carry[i+1] = g[i] OR (p_orig[i] AND carry[i])
  // But after prefix, g[i] = prefix generate = carry[i+1] when carry_in=0
  // So carry[i+1] = g[i] OR (p_all[i] AND carry_in)
  // Actually: after full prefix, g[i] represents G[i:0].
  // carry[i+1] = G[i:0] OR (P[i:0] AND carry_in)
  // But we overwrote p[i] during the prefix. We need original p[i] for sum.
  // Let me keep original p separately.

  // Redo with separate arrays
  std::vector<literalt> pg(n), pp(n);
  for(std::size_t i = 0; i < n; i++)
  {
    pg[i] = prop.land(op0[i], op1[i]);
    pp[i] = prop.lxor(op0[i], op1[i]);
  }
  std::vector<literalt> orig_p = pp;

  for(std::size_t lev = 0; lev < L; lev++)
  {
    std::size_t stride = std::size_t{1} << (lev + 1);
    std::size_t half = stride >> 1;
    for(std::size_t i = stride - 1; i < n; i += stride)
    {
      std::size_t j = i - half;
      pg[i] = prop.lor(pg[i], prop.land(pp[i], pg[j]));
      pp[i] = prop.land(pp[i], pp[j]);
    }
  }
  for(std::size_t lev = L - 1; lev >= 1; lev--)
  {
    std::size_t stride = std::size_t{1} << lev;
    std::size_t half = stride >> 1;
    for(std::size_t i = stride + half - 1; i < n; i += stride)
    {
      std::size_t j = i - half;
      pg[i] = prop.lor(pg[i], prop.land(pp[i], pg[j]));
    }
  }

  // Now pg[i] = G[i:0], the prefix generate
  // carry[i+1] = pg[i] OR (pp[i] AND carry_in)... no.
  // After prefix: pg[i] = G[i:0] which means carry[i+1] when carry_in=0.
  // Full carry: carry[0] = carry_in
  //             carry[i+1] = G[i:0] OR (P[i:0] AND carry_in)
  // But we only have P[i:0] for positions where pp was computed.
  // Simpler: carry[0] = carry_in, carry[i+1] = pg[i] (if carry_in=0)
  // For carry_in != 0: need to incorporate it.
  // Actually, handle carry_in by treating it as g[-1]=carry_in, p[-1]=false.
  // Then prefix from -1 to i gives the correct carry.
  // Easiest: just compute carry[i] = pg[i-1] OR (pp[i-1] AND carry_in) for i>0

  result.first.push_back(prop.lxor(orig_p[0], carry_in));
  for(std::size_t i = 1; i < n; i++)
  {
    literalt carry_i = prop.lor(pg[i - 1], prop.land(pp[i - 1], carry_in));
    result.first.push_back(prop.lxor(orig_p[i], carry_i));
  }
  result.second = prop.lor(pg[n - 1], prop.land(pp[n - 1], carry_in));
  return result;
}

std::pair<bvt, literalt>
bv_utilst::han_carlson_adder(
  const bvt &op0, const bvt &op1, literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());
  PRECONDITION(!op0.empty());

  std::size_t n = op0.size();
  std::vector<literalt> g(n), p(n);
  for(std::size_t i = 0; i < n; i++)
  {
    g[i] = prop.land(op0[i], op1[i]);
    p[i] = prop.lxor(op0[i], op1[i]);
  }
  std::vector<literalt> orig_p = p;

  // Han-Carlson: Kogge-Stone on odd-indexed bits, then one extra level
  // Step 1: First level merges adjacent pairs (all positions)
  {
    std::vector<literalt> ng = g, np = p;
    for(std::size_t i = 1; i < n; i += 2)
    {
      ng[i] = prop.lor(g[i], prop.land(p[i], g[i - 1]));
      np[i] = prop.land(p[i], p[i - 1]);
    }
    g = ng; p = np;
  }

  // Step 2: Kogge-Stone on odd-indexed bits only
  std::size_t L = address_bits(n);
  for(std::size_t lev = 1; lev < L; lev++)
  {
    std::size_t dist = std::size_t{1} << lev; // distance in original indexing
    std::vector<literalt> ng = g, np = p;
    for(std::size_t i = 1; i < n; i += 2)
    {
      if(i >= dist)
      {
        std::size_t j = i - dist;
        // j should be odd for KS on odd bits; if j is even, use j-1
        std::size_t src = (j % 2 == 1) ? j : (j > 0 ? j - 1 : 0);
        if(src < n)
        {
          ng[i] = prop.lor(g[i], prop.land(p[i], g[src]));
          np[i] = prop.land(p[i], p[src]);
        }
      }
    }
    g = ng; p = np;
  }

  // Step 3: Derive even-indexed carries from odd neighbors
  for(std::size_t i = 2; i < n; i += 2)
  {
    g[i] = prop.lor(g[i], prop.land(p[i], g[i - 1]));
  }

  // Compute sums
  std::pair<bvt, literalt> result;
  result.first.reserve(n);
  result.first.push_back(prop.lxor(orig_p[0], carry_in));
  for(std::size_t i = 1; i < n; i++)
  {
    literalt carry_i = prop.lor(g[i - 1], prop.land(p[i - 1], carry_in));
    result.first.push_back(prop.lxor(orig_p[i], carry_i));
  }
  result.second = prop.lor(g[n - 1], prop.land(p[n - 1], carry_in));
  return result;
}

std::pair<bvt, literalt>
bv_utilst::minimal_ripple_carry_adder(
  const bvt &op0, const bvt &op1, literalt carry_in)
{
  PRECONDITION(op0.size() == op1.size());

  // Minimal encoding: just sum and carry using the fewest possible
  // variables. Each bit: sum = a XOR b XOR c, carry = MAJ(a,b,c).
  // Use a single variable for carry (reused), and encode sum
  // directly as a XOR chain without an explicit variable when possible.
  //
  // For multiplication, many inputs are AND(x, constant_bit) which
  // are often 0. The XOR and MAJ simplify with constant propagation.
  //
  // Encoding per bit (non-constant case):
  //   carry_out = new_variable
  //   Majority clauses (carry_out = MAJ(a, b, carry_in)):
  //     !a | !b | carry_out          (any 2 true → carry 1)
  //     !a | !carry_in | carry_out
  //     !b | !carry_in | carry_out
  //     a | b | !carry_out            (any 2 false → carry 0)
  //     a | carry_in | !carry_out
  //     b | carry_in | !carry_out
  //   sum = a XOR b XOR carry_in (use prop.lxor chain)
  //   Total: 1 var for carry (6 clauses) + 2 vars for XOR (8 clauses)
  //   = 3 vars, 14 clauses — same as full_adder!
  //
  // Can we do fewer? Yes: encode carry WITHOUT a new variable
  // by using the sum variable and input variables.
  // carry_out = (a AND b) OR (carry_in AND (a XOR b))
  //           = (a AND b) OR (carry_in AND (sum XOR carry_in))
  // Hmm, that's circular.
  //
  // Alternative: don't create a carry variable at all.
  // Express carry implicitly through clauses relating consecutive sums.
  // This is what CLA does (24 clauses per bit, 0 carry vars).
  // But CLA has more clauses.
  //
  // Simplest reduction: use 1 variable for carry (6 clauses for MAJ)
  // and compute sum = a XOR b XOR carry_in using just 1 XOR variable
  // instead of 2 (chain of 2 XORs).
  // sum = a XOR b XOR carry_in can be encoded with 1 variable and
  // 8 clauses (direct 3-input XOR Tseitin encoding).
  // Total: 2 vars, 14 clauses — same as optimal full_adder.
  //
  // The optimal full_adder IS already minimal. But we can try:
  // skip the sum variable entirely and just track carries.
  // The sum is only needed for the output. For multiplication's
  // intermediate additions, only the final sum matters.
  // But CBMC needs all intermediate sums for the partial product
  // accumulation.
  //
  // Let me try the absolute minimum: 1 carry var with 6 MAJ clauses,
  // and reuse prop.lxor for sum (which does constant propagation).

  std::pair<bvt, literalt> result{bvt{}, carry_in};
  result.first.reserve(op0.size());
  literalt &c = result.second;

  for(std::size_t i = 0; i < op0.size(); i++)
  {
    literalt a = op0[i], b = op1[i];

    // Constant propagation
    if(a.is_false())
    {
      result.first.push_back(prop.lxor(b, c));
      c = prop.land(b, c);
      continue;
    }
    if(b.is_false())
    {
      result.first.push_back(prop.lxor(a, c));
      c = prop.land(a, c);
      continue;
    }
    if(c.is_false())
    {
      result.first.push_back(prop.lxor(a, b));
      c = prop.land(a, b);
      continue;
    }
    if(a.is_true())
    {
      result.first.push_back(prop.lequal(b, c));
      c = prop.lor(b, c);
      continue;
    }
    if(b.is_true())
    {
      result.first.push_back(prop.lequal(a, c));
      c = prop.lor(a, c);
      continue;
    }
    if(c.is_true())
    {
      result.first.push_back(prop.lequal(a, b));
      c = prop.lor(a, b);
      continue;
    }

    // General case: sum = XOR(a,b,c), carry = MAJ(a,b,c)
    // Use prop.lxor chain for sum (2 vars, 8 clauses)
    result.first.push_back(prop.lxor(prop.lxor(a, b), c));

    // Carry = MAJ(a,b,c) with direct 6-clause encoding
    literalt carry_out = prop.new_variable();
    prop.lcnf(!a, !b, carry_out);
    prop.lcnf(!a, !c, carry_out);
    prop.lcnf(!b, !c, carry_out);
    prop.lcnf(a, b, !carry_out);
    prop.lcnf(a, c, !carry_out);
    prop.lcnf(b, c, !carry_out);
    c = carry_out;
  }

  return result;
}

std::pair<bvt, literalt>
bv_utilst::sparse_brent_kung_adder(
  const bvt &op0, const bvt &op1, literalt carry_in)
{
  return brent_kung_adder(op0, op1, std::move(carry_in));
}

std::pair<bvt, literalt>
bv_utilst::adder(const bvt &op0, const bvt &op1, literalt carry_in)
{
  // Not an accumulation step — start fresh carry-save state
  switch(adder_encoding)
  {
  case adder_encodingt::SIMPLE_RIPPLE_CARRY:
    return simple_ripple_carry_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::BRENT_KUNG:
    return brent_kung_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::KOGGE_STONE:
    return kogge_stone_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::SKLANSKY:
    return sklansky_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::LADNER_FISCHER:
    return ladner_fischer_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::HAN_CARLSON:
    return han_carlson_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::MINIMAL_RIPPLE:
    return minimal_ripple_carry_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::SPARSE_BK:
    return sparse_brent_kung_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::CLA:
    return carry_lookahead_adder(op0, op1, std::move(carry_in));
  case adder_encodingt::ADAPTIVE:
  {
    // Ripple carry + redundant generate variables (g-only).
    // g[i] = a[i] AND b[i] triggers BVE cascade via polarity
    // alignment with the full_adder's carry generation clauses.
    if(op0.size() <= 4)
      return optimized_ripple_carry_adder(op0, op1, std::move(carry_in));
    std::size_t n = op0.size();
    auto result = optimized_ripple_carry_adder(op0, op1, carry_in);
    for(std::size_t i = 0; i < n; i++)
      prop.land(op0[i], op1[i]);
    return result;
  }
    case adder_encodingt::RIPPLE_CARRY:
  default:
    return optimized_ripple_carry_adder(op0, op1, std::move(carry_in));
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
  return adder_no_overflow(op0, op1, subtract, rep);
}

bvt bv_utilst::add_sub(const bvt &op0, const bvt &op1, bool subtract)
{
  PRECONDITION(op0.size() == op1.size());

  literalt carry_in=const_literal(subtract);

  bvt tmp_op1=subtract?inverted(op1):op1;

  // we ignore the carry-out
  return adder(op0, tmp_op1, carry_in).first;
}

bvt bv_utilst::add_sub(const bvt &op0, const bvt &op1, literalt subtract)
{
  const bvt op1_sign_applied=
    select(subtract, inverted(op1), op1);

  // we ignore the carry-out
  return adder(op0, op1_sign_applied, subtract).first;
}

bvt bv_utilst::saturating_add_sub(
  const bvt &op0,
  const bvt &op1,
  bool subtract,
  representationt rep)
{
  PRECONDITION(op0.size() == op1.size());
  PRECONDITION(
    rep == representationt::SIGNED || rep == representationt::UNSIGNED);

  literalt carry_in = const_literal(subtract);

  bvt tmp_op1 = subtract ? inverted(op1) : op1;

  auto add_sub_result = adder(op0, tmp_op1, carry_in);
  literalt carry_out = add_sub_result.second;

  bvt result;
  result.reserve(add_sub_result.first.size());
  if(rep == representationt::UNSIGNED)
  {
    // An unsigned overflow has occurred when carry_out is not equal to
    // subtract: addition with a carry-out means an overflow beyond the maximum
    // representable value, subtraction without a carry-out means an underflow
    // below zero. For saturating arithmetic the former implies that all bits
    // should be set to 1, in the latter case all bits should be set to zero.
    for(const auto &literal : add_sub_result.first)
    {
      result.push_back(
        subtract ? prop.land(literal, carry_out)
                 : prop.lor(literal, carry_out));
    }
  }
  else
  {
    // A signed overflow beyond the maximum representable value occurs when
    // adding two positive numbers and the wrap-around result being negative, or
    // when subtracting a negative from a positive number (and, again, the
    // result being negative).
    literalt overflow_to_max_int = prop.land(bvt{
      !sign_bit(op0),
      subtract ? sign_bit(op1) : !sign_bit(op1),
      sign_bit(add_sub_result.first)});
    // A signed underflow below the minimum representable value occurs when
    // adding two negative numbers and arriving at a positive result, or
    // subtracting a positive from a negative number (and, again, obtaining a
    // positive wrap-around result).
    literalt overflow_to_min_int = prop.land(bvt{
      sign_bit(op0),
      subtract ? !sign_bit(op1) : sign_bit(op1),
      !sign_bit(add_sub_result.first)});

    // set all bits except for the sign bit
    PRECONDITION(!add_sub_result.first.empty());
    for(std::size_t i = 0; i < add_sub_result.first.size() - 1; ++i)
    {
      const auto &literal = add_sub_result.first[i];
      result.push_back(prop.land(
        prop.lor(overflow_to_max_int, literal), !overflow_to_min_int));
    }
    // finally add the sign bit
    result.push_back(prop.land(
      prop.lor(overflow_to_min_int, sign_bit(add_sub_result.first)),
      !overflow_to_max_int));
  }

  return result;
}

literalt bv_utilst::overflow_add(
  const bvt &op0, const bvt &op1, representationt rep)
{
  if(rep==representationt::SIGNED)
  {
    // An overflow occurs if the signs of the two operands are the same
    // and the sign of the sum is the opposite.

    literalt old_sign = sign_bit(op0);
    literalt sign_the_same = prop.lequal(sign_bit(op0), sign_bit(op1));

    bvt result=add(op0, op1);
    return prop.land(sign_the_same, prop.lxor(sign_bit(result), old_sign));
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
    literalt op0_is_negative = sign_bit(op0);

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

bvt bv_utilst::adder_no_overflow(
  const bvt &op0,
  const bvt &op1,
  bool subtract,
  representationt rep)
{
  const bvt tmp_op = subtract ? inverted(op1) : op1;

  if(rep==representationt::SIGNED)
  {
    // an overflow occurs if the signs of the two operands are the same
    // and the sign of the sum is the opposite

    literalt old_sign = sign_bit(op0);
    literalt sign_the_same = prop.lequal(sign_bit(op0), sign_bit(tmp_op));

    // we ignore the carry-out
    bvt sum = adder(op0, tmp_op, const_literal(subtract)).first;

    prop.l_set_to_false(
      prop.land(sign_the_same, prop.lxor(sign_bit(sum), old_sign)));

    return sum;
  }
  else
  {
    INVARIANT(
      rep == representationt::UNSIGNED,
      "representation has either value signed or unsigned");
    auto result = adder(op0, tmp_op, const_literal(subtract));
    prop.l_set_to(result.second, subtract);
    return std::move(result.first);
  }
}

bvt bv_utilst::adder_no_overflow(const bvt &op0, const bvt &op1)
{
  return adder_no_overflow(op0, op1, false, representationt::UNSIGNED);
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
      l = dist < src.size() - i ? src[i + dist] : sign_bit(src);
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
  prop.l_set_to_false(overflow_negate(bv));
  return negate(bv);
}

literalt bv_utilst::overflow_negate(const bvt &bv)
{
  // a overflow on unary- can only happen with the smallest
  // representable number 100....0

  bvt should_be_zeros(bv);
  should_be_zeros.pop_back();

  return prop.land(sign_bit(bv), !prop.lor(should_be_zeros));
}

void bv_utilst::incrementer(
  bvt &bv,
  literalt carry_in,
  literalt &carry_out)
{
  carry_out=carry_in;

  for(auto &literal : bv)
  {
    literalt new_carry = prop.land(carry_out, literal);
    literal = prop.lxor(literal, carry_out);
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
  for(auto &literal : result)
    literal = !literal;
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

      bvt s, t(a.size(), const_literal(false));
      s.reserve(a.size());

      for(std::size_t bit=0; bit<a.size(); bit++)
      {
        literalt carry_out;
        s.push_back(full_adder(a[bit], b[bit], c[bit], carry_out));
        if(bit + 1 < a.size())
          t[bit + 1] = carry_out;
      }

      new_pps.push_back(std::move(s));
      new_pps.push_back(std::move(t));
    }

    // pass onwards up to two remaining partial products
    for(std::size_t i=no_full_adders*3; i<pps.size(); i++)
      new_pps.push_back(pps[i]);

    POSTCONDITION(new_pps.size() < pps.size());
    return wallace_tree(new_pps);
  }
}

bvt bv_utilst::dadda_tree(const std::vector<bvt> &pps)
{
  PRECONDITION(!pps.empty());

  using columnt = std::list<literalt>;
  std::vector<columnt> columns(pps.front().size());
  for(const auto &pp : pps)
  {
    PRECONDITION(pp.size() == pps.front().size());
    for(std::size_t i = 0; i < pp.size(); ++i)
    {
      if(!pp[i].is_false())
        columns[i].push_back(pp[i]);
    }
  }

  std::list<std::size_t> dadda_sequence;
  for(std::size_t d = 2; d < pps.front().size(); d = (d * 3) / 2)
    dadda_sequence.push_front(d);

  for(auto d : dadda_sequence)
  {
    for(auto col_it = columns.begin(); col_it != columns.end();) // no ++col_it
    {
      if(col_it->size() <= d)
        ++col_it;
      else if(col_it->size() == d + 1)
      {
        // Dadda prescribes a half adder here, but OPTIMAL_FULL_ADDER makes
        // full_adder actually build a half adder when carry-in is false.
        literalt carry_out;
        col_it->push_back(full_adder(
          col_it->front(),
          *std::next(col_it->begin()),
          const_literal(false),
          carry_out));
        col_it->pop_front();
        col_it->pop_front();
        if(std::next(col_it) != columns.end())
          std::next(col_it)->push_back(carry_out);
      }
      else
      {
        // We could also experiment with n:2 compressors (for n > 3, n=3 is the
        // full adder as used below) that use circuits with lower gate count
        // than just combining multiple full adders.
        literalt carry_out;
        col_it->push_back(full_adder(
          col_it->front(),
          *std::next(col_it->begin()),
          *std::next(std::next(col_it->begin())),
          carry_out));
        col_it->pop_front();
        col_it->pop_front();
        col_it->pop_front();
        if(std::next(col_it) != columns.end())
          std::next(col_it)->push_back(carry_out);
      }
    }
  }

  bvt a, b;
  a.reserve(pps.front().size());
  b.reserve(pps.front().size());

  for(const auto &col : columns)
  {
    PRECONDITION(col.size() <= 2);
    switch(col.size())
    {
    case 0:
      a.push_back(const_literal(false));
      b.push_back(const_literal(false));
      break;
    case 1:
      a.push_back(col.front());
      b.push_back(const_literal(false));
      break;
    case 2:
      a.push_back(col.front());
      b.push_back(col.back());
    }
  }

  return add(a, b);
}

bvt bv_utilst::comba_column_wise(const std::vector<bvt> &pps)
{
  PRECONDITION(!pps.empty());

  std::vector<bvt> columns(pps.front().size());
  for(const auto &pp : pps)
  {
    PRECONDITION(pp.size() == pps.front().size());
    for(std::size_t i = 0; i < pp.size(); ++i)
    {
      if(!pp[i].is_false())
        columns[i].push_back(pp[i]);
    }
  }

  bvt result;
  result.reserve(columns.size());

  for(std::size_t i = 0; i < columns.size(); ++i)
  {
    const bvt &column = columns[i];

    if(column.empty())
      result.push_back(const_literal(false));
    else
    {
      bvt column_sum = popcount(column);
      CHECK_RETURN(!column_sum.empty());
      result.push_back(column_sum.front());
      for(std::size_t j = 1; j < column_sum.size(); ++j)
      {
        if(i + j >= columns.size())
          break;
        if(!column_sum[j].is_false())
          columns[i + j].push_back(column_sum[j]);
      }
    }
  }

  return result;
}

// Wallace tree multiplier. This is disabled, as runtimes have
// been observed to go up by 5%-10%, and on some models even by 20%.
// #define WALLACE_TREE
// Dadda' reduction scheme. This yields a smaller formula size than Wallace
// trees (and also the default addition scheme), but isn't consistently more
// performant with simple partial-product generation. Only when using
// higher-radix multipliers the combination appears to perform better.
// #define DADDA_TREE

// The following examples demonstrate the performance differences (with a
// time-out of 7200 seconds):
//
// #ifndef BITWIDTH
// #define BITWIDTH 8
// #endif
//
// int main()
// {
//   __CPROVER_bitvector[BITWIDTH] a, b;
//   __CPROVER_assert(a * 3 == a + a + a, "multiplication by 3");
//   __CPROVER_assert(3 * a == a + a + a, "multiplication by 3");
//   __CPROVER_bitvector[BITWIDTH] ab = a * b;
//   __CPROVER_bitvector[BITWIDTH * 2] ab_check =
//     (__CPROVER_bitvector[BITWIDTH * 2])a *
//     (__CPROVER_bitvector[BITWIDTH * 2])b;
//   __CPROVER_assert(
//     ab == (__CPROVER_bitvector[BITWIDTH])ab_check, "should pass");
// }
//
// |----|-----------------------------|-----------------------------|
// |    |           CaDiCaL           |           MiniSat2          |
// |----|-----------------------------|-----------------------------|
// | n  | No tree | Wallace |  Dadda  | No tree | Wallace |  Dadda  |
// |----|---------|---------|---------|---------|---------|---------|
// |  1 |    0.00 |    0.00 |    0.00 |    0.00 |    0.00 |    0.00 |
// |  2 |    0.00 |    0.00 |    0.00 |    0.00 |    0.00 |    0.00 |
// |  3 |    0.01 |    0.01 |    0.00 |    0.00 |    0.00 |    0.00 |
// |  4 |    0.01 |    0.01 |    0.01 |    0.01 |    0.01 |    0.01 |
// |  5 |    0.04 |    0.04 |    0.04 |    0.01 |    0.01 |    0.01 |
// |  6 |    0.11 |    0.13 |    0.12 |    0.04 |    0.05 |    0.06 |
// |  7 |    0.28 |    0.46 |    0.44 |    0.15 |    0.27 |    0.31 |
// |  8 |    0.50 |    1.55 |    1.09 |    0.90 |    1.06 |    1.36 |
// |  9 |    2.22 |    3.63 |    2.67 |    3.40 |    5.85 |    3.44 |
// | 10 |    2.79 |    4.81 |    4.69 |    4.32 |   28.41 |   28.01 |
// | 11 |    8.48 |    4.45 |   11.99 |   38.24 |   98.55 |   86.46 |
// | 12 |   14.52 |    4.86 |    5.80 |  115.00 |  140.11 |  461.70 |
// | 13 |   33.62 |    5.56 |    6.14 |  210.24 |  805.59 |  609.01 |
// | 14 |   37.23 |    6.11 |    8.01 |  776.75 |  689.96 | 6153.82 |
// | 15 |  108.65 |    7.86 |   14.72 | 1048.92 | 1421.74 | 6881.78 |
// | 16 |  102.61 |   14.08 |   18.54 | 1628.01 | timeout | 1943.85 |
// | 17 |  117.89 |   18.53 |    9.19 | 4148.73 | timeout | timeout |
// | 18 |  209.40 |    7.97 |    7.74 | 2760.51 | timeout | timeout |
// | 19 |  168.21 |   18.04 |   15.00 | 2514.21 | timeout | timeout |
// | 20 |  566.76 |   12.68 |   22.47 | 2609.09 | timeout | timeout |
// | 21 |  786.31 |   23.80 |   23.80 | 2232.77 | timeout | timeout |
// | 22 |  817.74 |   17.64 |   22.53 | 3866.70 | timeout | timeout |
// | 23 | 1102.76 |   24.19 |   26.37 | timeout | timeout | timeout |
// | 24 | 1319.59 |   27.37 |   29.95 | timeout | timeout | timeout |
// | 25 | 1786.11 |   27.10 |   29.94 | timeout | timeout | timeout |
// | 26 | 1952.18 |   31.08 |   33.95 | timeout | timeout | timeout |
// | 27 | 6908.48 |   27.92 |   34.94 | timeout | timeout | timeout |
// | 28 | 6919.34 |   36.63 |   33.78 | timeout | timeout | timeout |
// | 29 | timeout |   27.95 |   40.69 | timeout | timeout | timeout |
// | 30 | timeout |   36.94 |   31.59 | timeout | timeout | timeout |
// | 31 | timeout |   38.41 |   40.04 | timeout | timeout | timeout |
// | 32 | timeout |   33.06 |   91.38 | timeout | timeout | timeout |
// |----|---------|---------|---------|---------|---------|---------|
//
// In summary, both Wallace tree and Dadda reduction are substantially more
// efficient with CaDiCaL on the above code for all bit width > 11, but somewhat
// slower with MiniSat.
//
// #ifndef BITWIDTH
// #define BITWIDTH 8
// #endif
//
// int main()
// {
//   __CPROVER_bitvector[BITWIDTH] a, b, c, ab, bc, abc;
//   ab = a * b;
//   __CPROVER_bitvector[BITWIDTH * 2] ab_check =
//     (__CPROVER_bitvector[BITWIDTH * 2])a *
//     (__CPROVER_bitvector[BITWIDTH * 2])b;
//   __CPROVER_assume(ab == ab_check);
//   bc = b * c;
//   __CPROVER_bitvector[BITWIDTH * 2] bc_check =
//     (__CPROVER_bitvector[BITWIDTH * 2])b *
//     (__CPROVER_bitvector[BITWIDTH * 2])c;
//   __CPROVER_assume(bc == bc_check);
//   abc = ab * c;
//   __CPROVER_bitvector[BITWIDTH * 2] abc_check =
//     (__CPROVER_bitvector[BITWIDTH * 2])ab *
//     (__CPROVER_bitvector[BITWIDTH * 2])c;
//   __CPROVER_assume(abc == abc_check);
//   __CPROVER_assert(abc == a * bc, "associativity");
// }
//
// |----|-----------------------------|-----------------------------|
// |    |           CaDiCaL           |           MiniSat2          |
// |----|-----------------------------|-----------------------------|
// | n  | No tree | Wallace |  Dadda  | No tree | Wallace |  Dadda  |
// |----|---------|---------|---------|---------|---------|---------|
// |  1 |    0.00 |    0.00 |    0.00 |    0.01 |    0.01 |    0.01 |
// |  2 |    0.01 |    0.01 |    0.01 |    0.01 |    0.01 |    0.01 |
// |  3 |    0.02 |    0.03 |    0.03 |    0.01 |    0.01 |    0.01 |
// |  4 |    0.05 |    0.07 |    0.06 |    0.02 |    0.02 |    0.02 |
// |  5 |    0.17 |    0.18 |    0.14 |    0.04 |    0.04 |    0.04 |
// |  6 |    0.50 |    0.63 |    0.63 |    0.13 |    0.14 |    0.13 |
// |  7 |    1.01 |    1.15 |    0.90 |    0.43 |    0.47 |    0.47 |
// |  8 |    1.56 |    1.76 |    1.75 |    3.35 |    2.39 |    1.75 |
// |  9 |    2.07 |    2.48 |    1.75 |   11.20 |   12.64 |    7.94 |
// | 10 |    3.58 |    3.88 |    3.54 |   20.23 |   23.49 |   15.66 |
// | 11 |    5.84 |    7.46 |    5.31 |   49.32 |   39.86 |   44.15 |
// | 12 |   11.71 |   16.85 |   13.40 |   69.32 |  156.57 |   46.50 |
// | 13 |   33.22 |   41.95 |   34.43 |  250.91 |  294.73 |   79.47 |
// | 14 |   76.27 |  109.59 |   84.49 |  226.98 |  259.84 |  258.08 |
// | 15 |  220.01 |  330.10 |  267.11 |  783.73 | 1160.47 | 1262.91 |
// | 16 |  591.91 |  981.16 |  808.33 | 2712.20 | 4286.60 | timeout |
// | 17 | 1634.97 | 2574.81 | 2006.27 | timeout | timeout | timeout |
// | 18 | 4680.16 | timeout | 6704.35 | timeout | timeout | timeout |
// | 19 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 20 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 21 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 22 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 23 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 24 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 25 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 26 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 27 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 28 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 29 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 30 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 31 | timeout | timeout | timeout | timeout | timeout | timeout |
// | 32 | timeout | timeout | timeout | timeout | timeout | timeout |
// |----|---------|---------|---------|---------|---------|---------|
//
// In summary, Wallace tree reduction is slower for both solvers and all bit
// widths (except BITWIDTH==8 with MiniSat2). Dadda multipliers get closer to
// our multiplier that's not using a tree reduction scheme, but aren't uniformly
// better either.

// Higher radix multipliers pre-compute partial products for groups of bits:
// radix-4 are groups of 2 bits, radix-8 are groups of 3 bits, and radix-16 are
// groups of 4 bits. Performance data for these variants combined with different
// (tree) reduction schemes are recorded at
// https://tinyurl.com/multiplier-comparison. The data suggests that radix-8
// with Dadda's reduction yields the most consistent performance improvement
// while not regressing substantially in the matrix of different benchmarks and
// CaDiCaL and MiniSat2 as solvers.
// #define RADIX_MULTIPLIER 8
// #define USE_KARATSUBA
// #define USE_TOOM_COOK
// #define USE_SCHOENHAGE_STRASSEN
#ifdef RADIX_MULTIPLIER
#  define DADDA_TREE
#endif
#define COMBA

#ifdef RADIX_MULTIPLIER
static bvt unsigned_multiply_by_3(propt &prop, const bvt &op)
{
  PRECONDITION(prop.cnf_handled_well());
  PRECONDITION(!op.empty());

  bvt result;
  result.reserve(op.size());

  result.push_back(op[0]);
  literalt prev_bit = const_literal(false);

  for(std::size_t i = 1; i < op.size(); ++i)
  {
    literalt sum = prop.new_variable();

    prop.lcnf({sum, !op[i - 1], !op[i], !prev_bit});
    prop.lcnf({sum, !op[i - 1], !op[i], result.back()});
    prop.lcnf({sum, op[i - 1], op[i], !prev_bit, result.back()});
    prop.lcnf({sum, !op[i - 1], op[i], prev_bit, !result.back()});
    prop.lcnf({sum, op[i - 1], !op[i], !result.back()});
    prop.lcnf({sum, op[i - 1], !op[i], prev_bit});

    prop.lcnf({!sum, !op[i - 1], op[i], !prev_bit});
    prop.lcnf({!sum, !op[i - 1], op[i], result.back()});
    prop.lcnf({!sum, !op[i - 1], !op[i], prev_bit, !result.back()});

    prop.lcnf({!sum, op[i - 1], op[i], !result.back()});
    prop.lcnf({!sum, op[i - 1], op[i], prev_bit});
    prop.lcnf({!sum, op[i - 1], !op[i], !prev_bit, result.back()});

    prop.lcnf({!sum, op[i], prev_bit, result.back()});
    prop.lcnf({!sum, op[i], !prev_bit, !result.back()});

    result.push_back(sum);
    prev_bit = op[i - 1];
  }

  return result;
}
#endif

bvt bv_utilst::unsigned_multiplier(const bvt &_op0, const bvt &_op1)
{
  PRECONDITION(!_op0.empty());
  PRECONDITION(!_op1.empty());

  if(_op1.size() == 1)
  {
    bvt product;
    product.reserve(_op0.size());
    for(const auto &lit : _op0)
      product.push_back(prop.land(lit, _op1.front()));
    return product;
  }

  // store partial products
  std::vector<bvt> pps;
  pps.reserve(_op0.size());

  bvt op0 = _op0, op1 = _op1;

#ifndef RADIX_MULTIPLIER
  if(is_constant(op1))
    std::swap(op0, op1);

  for(std::size_t bit=0; bit<op0.size(); bit++)
  {
    if(op0[bit] == const_literal(false))
      continue;

    // zeros according to weight
    bvt pp = zeros(bit);
    pp.reserve(op0.size());

    for(std::size_t idx = bit; idx < op0.size(); idx++)
      pp.push_back(prop.land(op1[idx - bit], op0[bit]));

    pps.push_back(pp);
  }
#else
#  if RADIX_MULTIPLIER == 4
#    define RADIX_GROUP_SIZE 2
#  elif RADIX_MULTIPLIER == 8
#    define RADIX_GROUP_SIZE 3
#  elif RADIX_MULTIPLIER == 16
#    define RADIX_GROUP_SIZE 4
#  else
#    error Unsupported radix
#  endif
  if(is_constant(op0) && !is_constant(op1))
    std::swap(op0, op1);

  std::optional<bvt> times_three_opt;
  auto times_three = [this, &times_three_opt, &op0]() -> const bvt &
  {
    if(!times_three_opt.has_value())
    {
#  if 1
      if(prop.cnf_handled_well())
        times_three_opt = unsigned_multiply_by_3(prop, op0);
      else
#  endif
        times_three_opt = add(op0, shift(op0, shiftt::SHIFT_LEFT, 1));
    }
    return *times_three_opt;
  };

#  if RADIX_MULTIPLIER >= 8
  std::optional<bvt> times_five_opt, times_seven_opt;
  auto times_five = [this, &times_five_opt, &op0]() -> const bvt &
  {
    if(!times_five_opt.has_value())
      times_five_opt = add(op0, shift(op0, shiftt::SHIFT_LEFT, 2));
    return *times_five_opt;
  };
  auto times_seven =
    [this, &times_seven_opt, &op0, &times_three]() -> const bvt &
  {
    if(!times_seven_opt.has_value())
      times_seven_opt = add(times_three(), shift(op0, shiftt::SHIFT_LEFT, 2));
    return *times_seven_opt;
  };
#  endif

#  if RADIX_MULTIPLIER == 16
  std::optional<bvt> times_nine_opt, times_eleven_opt, times_thirteen_opt,
    times_fifteen_opt;
  auto times_nine = [this, &times_nine_opt, &op0]() -> const bvt &
  {
    if(!times_nine_opt.has_value())
      times_nine_opt = add(op0, shift(op0, shiftt::SHIFT_LEFT, 3));
    return *times_nine_opt;
  };
  auto times_eleven =
    [this, &times_eleven_opt, &op0, &times_three]() -> const bvt &
  {
    if(!times_eleven_opt.has_value())
      times_eleven_opt = add(times_three(), shift(op0, shiftt::SHIFT_LEFT, 3));
    return *times_eleven_opt;
  };
  auto times_thirteen =
    [this, &times_thirteen_opt, &op0, &times_five]() -> const bvt &
  {
    if(!times_thirteen_opt.has_value())
      times_thirteen_opt = add(times_five(), shift(op0, shiftt::SHIFT_LEFT, 3));
    return *times_thirteen_opt;
  };
  auto times_fifteen =
    [this, &times_fifteen_opt, &op0, &times_seven]() -> const bvt &
  {
    if(!times_fifteen_opt.has_value())
      times_fifteen_opt = add(times_seven(), shift(op0, shiftt::SHIFT_LEFT, 3));
    return *times_fifteen_opt;
  };
#  endif

  for(std::size_t op1_idx = 0; op1_idx + RADIX_GROUP_SIZE - 1 < op1.size();
      op1_idx += RADIX_GROUP_SIZE)
  {
    const literalt &bit0 = op1[op1_idx];
    const literalt &bit1 = op1[op1_idx + 1];
#  if RADIX_MULTIPLIER >= 8
    const literalt &bit2 = op1[op1_idx + 2];
#    if RADIX_MULTIPLIER == 16
    const literalt &bit3 = op1[op1_idx + 3];
#    endif
#  endif
    bvt partial_sum;

    if(
      bit0.is_constant() && bit1.is_constant()
#  if RADIX_MULTIPLIER >= 8
      && bit2.is_constant()
#    if RADIX_MULTIPLIER == 16
      && bit3.is_constant()
#    endif
#  endif
    )
    {
      if(bit0.is_false()) // *0
      {
        if(bit1.is_false()) // *00
        {
#  if RADIX_MULTIPLIER >= 8
          if(bit2.is_false()) // *000
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0000
              continue;
            else // 1000
              partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx + 3);
#    else
            continue;
#    endif
          }
          else // *100
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0100
              partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx + 2);
            else // 1100
              partial_sum =
                shift(times_three(), shiftt::SHIFT_LEFT, op1_idx + 2);
#    else
            partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx + 2);
#    endif
          }
#  else
          continue;
#  endif
        }
        else // *10
        {
#  if RADIX_MULTIPLIER >= 8
          if(bit2.is_false()) // *010
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0010
              partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx + 1);
            else // 1010
              partial_sum =
                shift(times_five(), shiftt::SHIFT_LEFT, op1_idx + 1);
#    else
            partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx + 1);
#    endif
          }
          else // *110
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0110
              partial_sum =
                shift(times_three(), shiftt::SHIFT_LEFT, op1_idx + 1);
            else // 1110
              partial_sum =
                shift(times_seven(), shiftt::SHIFT_LEFT, op1_idx + 1);
#    else
            partial_sum = shift(times_three(), shiftt::SHIFT_LEFT, op1_idx + 1);
#    endif
          }
#  else
          partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx + 1);
#  endif
        }
      }
      else // *1
      {
        if(bit1.is_false()) // *01
        {
#  if RADIX_MULTIPLIER >= 8
          if(bit2.is_false()) // *001
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0001
              partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx);
            else // 1001
              partial_sum = shift(times_nine(), shiftt::SHIFT_LEFT, op1_idx);
#    else
            partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx);
#    endif
          }
          else // *101
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0101
              partial_sum = shift(times_five(), shiftt::SHIFT_LEFT, op1_idx);
            else // 1101
              partial_sum =
                shift(times_thirteen(), shiftt::SHIFT_LEFT, op1_idx);
#    else
            partial_sum = shift(times_five(), shiftt::SHIFT_LEFT, op1_idx);
#    endif
          }
#  else
          partial_sum = shift(op0, shiftt::SHIFT_LEFT, op1_idx);
#  endif
        }
        else // *11
        {
#  if RADIX_MULTIPLIER >= 8
          if(bit2.is_false()) // *011
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0011
              partial_sum = shift(times_three(), shiftt::SHIFT_LEFT, op1_idx);
            else // 1011
              partial_sum = shift(times_eleven(), shiftt::SHIFT_LEFT, op1_idx);
#    else
            partial_sum = shift(times_three(), shiftt::SHIFT_LEFT, op1_idx);
#    endif
          }
          else // *111
          {
#    if RADIX_MULTIPLIER == 16
            if(bit3.is_false()) // 0111
              partial_sum = shift(times_seven(), shiftt::SHIFT_LEFT, op1_idx);
            else // 1111
              partial_sum = shift(times_fifteen(), shiftt::SHIFT_LEFT, op1_idx);
#    else
            partial_sum = shift(times_seven(), shiftt::SHIFT_LEFT, op1_idx);
#    endif
          }
#  else
          partial_sum = shift(times_three(), shiftt::SHIFT_LEFT, op1_idx);
#  endif
        }
      }
    }
    else
    {
      partial_sum = bvt(op1_idx, const_literal(false));
      for(std::size_t op0_idx = 0; op0_idx + op1_idx < op0.size(); ++op0_idx)
      {
#  if RADIX_MULTIPLIER == 4
        if(prop.cnf_handled_well())
        {
          literalt partial_sum_bit = prop.new_variable();
          partial_sum.push_back(partial_sum_bit);

          // 00
          prop.lcnf({bit0, bit1, !partial_sum_bit});
          // 01 -> sum = _op0
          prop.lcnf({!bit0, bit1, !partial_sum_bit, _op0[op0_idx]});
          prop.lcnf({!bit0, bit1, partial_sum_bit, !_op0[op0_idx]});
          // 10 -> sum = (_op0 << 1)
          if(op0_idx == 0)
            prop.lcnf({bit0, !bit1, !partial_sum_bit});
          else
          {
            prop.lcnf({bit0, !bit1, !partial_sum_bit, _op0[op0_idx - 1]});
            prop.lcnf({bit0, !bit1, partial_sum_bit, !_op0[op0_idx - 1]});
          }
          // 11 -> sum = times_three
          prop.lcnf({!bit0, !bit1, !partial_sum_bit, times_three()[op0_idx]});
          prop.lcnf({!bit0, !bit1, partial_sum_bit, !times_three()[op0_idx]});
        }
        else
        {
          partial_sum.push_back(prop.lselect(
            !bit1,
            prop.land(bit0, op0[op0_idx]), // 0x
            prop.lselect(                  // 1x
              !bit0,
              op0_idx == 0 ? const_literal(false) : op0[op0_idx - 1],
              times_three()[op0_idx])));
        }
#  elif RADIX_MULTIPLIER == 8
        if(prop.cnf_handled_well())
        {
          literalt partial_sum_bit = prop.new_variable();
          partial_sum.push_back(partial_sum_bit);

          // 000
          prop.lcnf({bit0, bit1, bit2, !partial_sum_bit});
          // 001 -> sum = _op0
          prop.lcnf({!bit0, bit1, bit2, !partial_sum_bit, _op0[op0_idx]});
          prop.lcnf({!bit0, bit1, bit2, partial_sum_bit, !_op0[op0_idx]});
          // 010 -> sum = (_op0 << 1)
          if(op0_idx == 0)
            prop.lcnf({bit0, !bit1, bit2, !partial_sum_bit});
          else
          {
            prop.lcnf({bit0, !bit1, bit2, !partial_sum_bit, _op0[op0_idx - 1]});
            prop.lcnf({bit0, !bit1, bit2, partial_sum_bit, !_op0[op0_idx - 1]});
          }
          // 011 -> sum = times_three
          prop.lcnf(
            {!bit0, !bit1, bit2, !partial_sum_bit, times_three()[op0_idx]});
          prop.lcnf(
            {!bit0, !bit1, bit2, partial_sum_bit, !times_three()[op0_idx]});
          // 100 -> sum = (_op0 << 2)
          if(op0_idx == 0 || op0_idx == 1)
            prop.lcnf({bit0, bit1, !bit2, !partial_sum_bit});
          else
          {
            prop.lcnf({bit0, bit1, !bit2, !partial_sum_bit, _op0[op0_idx - 2]});
            prop.lcnf({bit0, bit1, !bit2, partial_sum_bit, !_op0[op0_idx - 2]});
          }
          // 101 -> sum = times_five
          prop.lcnf(
            {!bit0, bit1, !bit2, !partial_sum_bit, times_five()[op0_idx]});
          prop.lcnf(
            {!bit0, bit1, !bit2, partial_sum_bit, !times_five()[op0_idx]});
          // 110 -> sum = (times_three << 1)
          if(op0_idx == 0)
            prop.lcnf({bit0, !bit1, !bit2, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0,
               !bit1,
               !bit2,
               !partial_sum_bit,
               times_three()[op0_idx - 1]});
            prop.lcnf(
              {bit0,
               !bit1,
               !bit2,
               partial_sum_bit,
               !times_three()[op0_idx - 1]});
          }
          // 111 -> sum = times_seven
          prop.lcnf(
            {!bit0, !bit1, !bit2, !partial_sum_bit, times_seven()[op0_idx]});
          prop.lcnf(
            {!bit0, !bit1, !bit2, partial_sum_bit, !times_seven()[op0_idx]});
        }
        else
        {
          partial_sum.push_back(prop.lselect(
            !bit2,
            prop.lselect( // 0*
              !bit1,
              prop.land(bit0, op0[op0_idx]), // 00x
              prop.lselect(                  // 01x
                !bit0,
                op0_idx == 0 ? const_literal(false) : op0[op0_idx - 1],
                times_three()[op0_idx])),
            prop.lselect( // 1*
              !bit1,
              prop.lselect( // 10x
                !bit0,
                op0_idx <= 1 ? const_literal(false) : op0[op0_idx - 2],
                times_five()[op0_idx]),
              prop.lselect( // 11x
                !bit0,
                op0_idx == 0 ? const_literal(false)
                             : times_three()[op0_idx - 1],
                times_seven()[op0_idx]))));
        }
#  elif RADIX_MULTIPLIER == 16
        if(prop.cnf_handled_well())
        {
          literalt partial_sum_bit = prop.new_variable();
          partial_sum.push_back(partial_sum_bit);

          // 0000
          prop.lcnf({bit0, bit1, bit2, bit3, !partial_sum_bit});
          // 0001 -> sum = op0
          prop.lcnf({!bit0, bit1, bit2, bit3, !partial_sum_bit, op0[op0_idx]});
          prop.lcnf({!bit0, bit1, bit2, bit3, partial_sum_bit, !op0[op0_idx]});
          // 0010 -> sum = (op0 << 1)
          if(op0_idx == 0)
            prop.lcnf({bit0, !bit1, bit2, bit3, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0, !bit1, bit2, bit3, !partial_sum_bit, op0[op0_idx - 1]});
            prop.lcnf(
              {bit0, !bit1, bit2, bit3, partial_sum_bit, !op0[op0_idx - 1]});
          }
          // 0011 -> sum = times_three
          prop.lcnf(
            {!bit0,
             !bit1,
             bit2,
             bit3,
             !partial_sum_bit,
             times_three()[op0_idx]});
          prop.lcnf(
            {!bit0,
             !bit1,
             bit2,
             bit3,
             partial_sum_bit,
             !times_three()[op0_idx]});
          // 0100 -> sum = (op0 << 2)
          if(op0_idx == 0 || op0_idx == 1)
            prop.lcnf({bit0, bit1, !bit2, bit3, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0, bit1, !bit2, bit3, !partial_sum_bit, op0[op0_idx - 2]});
            prop.lcnf(
              {bit0, bit1, !bit2, bit3, partial_sum_bit, !op0[op0_idx - 2]});
          }
          // 0101 -> sum = times_five
          prop.lcnf(
            {!bit0,
             bit1,
             !bit2,
             bit3,
             !partial_sum_bit,
             times_five()[op0_idx]});
          prop.lcnf(
            {!bit0,
             bit1,
             !bit2,
             bit3,
             partial_sum_bit,
             !times_five()[op0_idx]});
          // 0110 -> sum = (times_three << 1)
          if(op0_idx == 0)
            prop.lcnf({bit0, !bit1, !bit2, bit3, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0,
               !bit1,
               !bit2,
               bit3,
               !partial_sum_bit,
               times_three()[op0_idx - 1]});
            prop.lcnf(
              {bit0,
               !bit1,
               !bit2,
               bit3,
               partial_sum_bit,
               !times_three()[op0_idx - 1]});
          }
          // 0111 -> sum = times_seven
          prop.lcnf(
            {!bit0,
             !bit1,
             !bit2,
             bit3,
             !partial_sum_bit,
             times_seven()[op0_idx]});
          prop.lcnf(
            {!bit0,
             !bit1,
             !bit2,
             bit3,
             partial_sum_bit,
             !times_seven()[op0_idx]});

          // 1000 -> sum = (op0 << 3)
          if(op0_idx == 0 || op0_idx == 1 || op0_idx == 2)
            prop.lcnf({bit0, bit1, bit2, !bit3, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0, bit1, bit2, !bit3, !partial_sum_bit, op0[op0_idx - 3]});
            prop.lcnf(
              {bit0, bit1, bit2, !bit3, partial_sum_bit, !op0[op0_idx - 3]});
          }
          // 1001 -> sum = times_nine
          prop.lcnf(
            {!bit0,
             bit1,
             bit2,
             !bit3,
             !partial_sum_bit,
             times_nine()[op0_idx]});
          prop.lcnf(
            {!bit0,
             bit1,
             bit2,
             !bit3,
             partial_sum_bit,
             !times_nine()[op0_idx]});
          // 1010 -> sum = (times_five << 1)
          if(op0_idx == 0)
            prop.lcnf({bit0, !bit1, bit2, !bit3, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0,
               !bit1,
               bit2,
               !bit3,
               !partial_sum_bit,
               times_five()[op0_idx - 1]});
            prop.lcnf(
              {bit0,
               !bit1,
               bit2,
               !bit3,
               partial_sum_bit,
               !times_five()[op0_idx - 1]});
          }
          // 1011 -> sum = times_eleven
          prop.lcnf(
            {!bit0,
             !bit1,
             bit2,
             !bit3,
             !partial_sum_bit,
             times_eleven()[op0_idx]});
          prop.lcnf(
            {!bit0,
             !bit1,
             bit2,
             !bit3,
             partial_sum_bit,
             !times_eleven()[op0_idx]});
          // 1100 -> sum = (times_three << 2)
          if(op0_idx == 0 || op0_idx == 1)
            prop.lcnf({bit0, bit1, !bit2, !bit3, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0,
               bit1,
               !bit2,
               !bit3,
               !partial_sum_bit,
               times_three()[op0_idx - 2]});
            prop.lcnf(
              {bit0,
               bit1,
               !bit2,
               !bit3,
               partial_sum_bit,
               !times_three()[op0_idx - 2]});
          }
          // 1101 -> sum = times_thirteen
          prop.lcnf(
            {!bit0,
             bit1,
             !bit2,
             !bit3,
             !partial_sum_bit,
             times_thirteen()[op0_idx]});
          prop.lcnf(
            {!bit0,
             bit1,
             !bit2,
             !bit3,
             partial_sum_bit,
             !times_thirteen()[op0_idx]});
          // 1110 -> sum = (times_seven << 1)
          if(op0_idx == 0)
            prop.lcnf({bit0, !bit1, !bit2, !bit3, !partial_sum_bit});
          else
          {
            prop.lcnf(
              {bit0,
               !bit1,
               !bit2,
               !bit3,
               !partial_sum_bit,
               times_seven()[op0_idx - 1]});
            prop.lcnf(
              {bit0,
               !bit1,
               !bit2,
               !bit3,
               partial_sum_bit,
               !times_seven()[op0_idx - 1]});
          }
          // 1111 -> sum = times_fifteen
          prop.lcnf(
            {!bit0,
             !bit1,
             !bit2,
             !bit3,
             !partial_sum_bit,
             times_fifteen()[op0_idx]});
          prop.lcnf(
            {!bit0,
             !bit1,
             !bit2,
             !bit3,
             partial_sum_bit,
             !times_fifteen()[op0_idx]});
        }
        else
        {
          partial_sum.push_back(prop.lselect(
            !bit3,
            prop.lselect( // 0*
              !bit2,
              prop.lselect( // 00*
                !bit1,
                prop.land(bit0, op0[op0_idx]), // 000x
                prop.lselect(                  // 001x
                  !bit0,
                  op0_idx == 0 ? const_literal(false) : op0[op0_idx - 1],
                  times_three()[op0_idx])),
              prop.lselect( // 01*
                !bit1,
                prop.lselect( // 010x
                  !bit0,
                  op0_idx <= 1 ? const_literal(false) : op0[op0_idx - 2],
                  times_five()[op0_idx]),
                prop.lselect( // 011x
                  !bit0,
                  op0_idx == 0 ? const_literal(false)
                               : times_three()[op0_idx - 1],
                  times_seven()[op0_idx]))),
            prop.lselect( // 1*
              !bit2,
              prop.lselect( // 10*
                !bit1,
                prop.lselect( // 100x
                  !bit0,
                  op0_idx <= 2 ? const_literal(false) : op0[op0_idx - 3],
                  times_nine()[op0_idx]),
                prop.lselect( // 101x
                  !bit0,
                  op0_idx == 0 ? const_literal(false)
                               : times_five()[op0_idx - 1],
                  times_eleven()[op0_idx])),
              prop.lselect( // 11*
                !bit1,
                prop.lselect( // 110x
                  !bit0,
                  op0_idx <= 1 ? const_literal(false)
                               : times_three()[op0_idx - 2],
                  times_thirteen()[op0_idx]),
                prop.lselect( // 111x
                  !bit0,
                  op0_idx == 0 ? const_literal(false)
                               : times_seven()[op0_idx - 1],
                  times_fifteen()[op0_idx])))));
        }
#  else
#    error Unsupported radix
#  endif
      }
    }

    pps.push_back(std::move(partial_sum));
  }

  if(op1.size() % RADIX_GROUP_SIZE == 1)
  {
    if(op0.size() == op1.size())
    {
      if(pps.empty())
        pps.push_back(bvt(op0.size(), const_literal(false)));

      // This is the partial product of the MSB of op1 with op0, which is all
      // zeros except for (possibly) the MSB. Since we don't need to account for
      // any carry out of adding this partial product, we just need to compute
      // the sum the MSB of one of the partial products and this partial
      // product, we is an xor of just those bits.
      pps.back().back() =
        prop.lxor(pps.back().back(), prop.land(op0[0], op1.back()));
    }
    else
    {
      bvt partial_sum = bvt(op1.size() - 1, const_literal(false));
      for(const auto &lit : op0)
      {
        partial_sum.push_back(prop.land(lit, op1.back()));
        if(partial_sum.size() == op0.size())
          break;
      }
      pps.push_back(std::move(partial_sum));
    }
  }
#  if RADIX_MULTIPLIER >= 8
  else if(op1.size() % RADIX_GROUP_SIZE == 2)
  {
    const literalt &bit0 = op1[op1.size() - 2];
    const literalt &bit1 = op1[op1.size() - 1];

    bvt partial_sum = bvt(op1.size() - 2, const_literal(false));
    for(std::size_t op0_idx = 0; op0_idx < 2; ++op0_idx)
    {
      if(prop.cnf_handled_well())
      {
        literalt partial_sum_bit = prop.new_variable();
        partial_sum.push_back(partial_sum_bit);
        // 00
        prop.lcnf({bit0, bit1, !partial_sum_bit});
        // 01 -> sum = op0
        prop.lcnf({!bit0, bit1, !partial_sum_bit, op0[op0_idx]});
        prop.lcnf({!bit0, bit1, partial_sum_bit, !op0[op0_idx]});
        // 10 -> sum = (op0 << 1)
        if(op0_idx == 0)
          prop.lcnf({bit0, !bit1, !partial_sum_bit});
        else
        {
          prop.lcnf({bit0, !bit1, !partial_sum_bit, op0[op0_idx - 1]});
          prop.lcnf({bit0, !bit1, partial_sum_bit, !op0[op0_idx - 1]});
        }
        // 11 -> sum = times_three
        prop.lcnf({!bit0, !bit1, !partial_sum_bit, times_three()[op0_idx]});
        prop.lcnf({!bit0, !bit1, partial_sum_bit, !times_three()[op0_idx]});
      }
      else
      {
        partial_sum.push_back(prop.lselect(
          !bit1,
          prop.land(bit0, op0[op0_idx]), // 0x
          prop.lselect(                  // 1x
            !bit0,
            op0_idx == 0 ? const_literal(false) : op0[op0_idx - 1],
            times_three()[op0_idx])));
      }
    }

    pps.push_back(std::move(partial_sum));
  }
#  endif
#  if RADIX_MULTIPLIER == 16
  else if(op1.size() % RADIX_GROUP_SIZE == 3)
  {
    const literalt &bit0 = op1[op1.size() - 3];
    const literalt &bit1 = op1[op1.size() - 2];
    const literalt &bit2 = op1[op1.size() - 1];

    bvt partial_sum = bvt(op1.size() - 3, const_literal(false));
    for(std::size_t op0_idx = 0; op0_idx < 3; ++op0_idx)
    {
      if(prop.cnf_handled_well())
      {
        literalt partial_sum_bit = prop.new_variable();
        partial_sum.push_back(partial_sum_bit);
        // 000
        prop.lcnf({bit0, bit1, bit2, !partial_sum_bit});
        // 001 -> sum = op0
        prop.lcnf({!bit0, bit1, bit2, !partial_sum_bit, op0[op0_idx]});
        prop.lcnf({!bit0, bit1, bit2, partial_sum_bit, !op0[op0_idx]});
        // 010 -> sum = (op0 << 1)
        if(op0_idx == 0)
          prop.lcnf({bit0, !bit1, bit2, !partial_sum_bit});
        else
        {
          prop.lcnf({bit0, !bit1, bit2, !partial_sum_bit, op0[op0_idx - 1]});
          prop.lcnf({bit0, !bit1, bit2, partial_sum_bit, !op0[op0_idx - 1]});
        }
        // 011 -> sum = times_three
        prop.lcnf(
          {!bit0, !bit1, bit2, !partial_sum_bit, times_three()[op0_idx]});
        prop.lcnf(
          {!bit0, !bit1, bit2, partial_sum_bit, !times_three()[op0_idx]});
        // 100 -> sum = (op0 << 2)
        if(op0_idx == 0 || op0_idx == 1)
          prop.lcnf({bit0, bit1, !bit2, !partial_sum_bit});
        else
        {
          prop.lcnf({bit0, bit1, !bit2, !partial_sum_bit, op0[op0_idx - 2]});
          prop.lcnf({bit0, bit1, !bit2, partial_sum_bit, !op0[op0_idx - 2]});
        }
        // 101 -> sum = times_five
        prop.lcnf(
          {!bit0, bit1, !bit2, !partial_sum_bit, times_five()[op0_idx]});
        prop.lcnf(
          {!bit0, bit1, !bit2, partial_sum_bit, !times_five()[op0_idx]});
        // 110 -> sum = (times_three << 1)
        if(op0_idx == 0)
          prop.lcnf({bit0, !bit1, !bit2, !partial_sum_bit});
        else
        {
          prop.lcnf(
            {bit0, !bit1, !bit2, !partial_sum_bit, times_three()[op0_idx - 1]});
          prop.lcnf(
            {bit0, !bit1, !bit2, partial_sum_bit, !times_three()[op0_idx - 1]});
        }
        // 111 -> sum = times_seven
        prop.lcnf(
          {!bit0, !bit1, !bit2, !partial_sum_bit, times_seven()[op0_idx]});
        prop.lcnf(
          {!bit0, !bit1, !bit2, partial_sum_bit, !times_seven()[op0_idx]});
      }
      else
      {
        partial_sum.push_back(prop.lselect(
          !bit2,
          prop.lselect( // 0*
            !bit1,
            prop.land(bit0, op0[op0_idx]), // 00x
            prop.lselect(                  // 01x
              !bit0,
              op0_idx == 0 ? const_literal(false) : op0[op0_idx - 1],
              times_three()[op0_idx])),
          prop.lselect( // 1*
            !bit1,
            prop.lselect( // 10x
              !bit0,
              op0_idx <= 1 ? const_literal(false) : op0[op0_idx - 2],
              times_five()[op0_idx]),
            prop.lselect( // 11x
              !bit0,
              op0_idx == 0 ? const_literal(false) : times_three()[op0_idx - 1],
              times_seven()[op0_idx]))));
      }
    }

    pps.push_back(std::move(partial_sum));
  }
#  endif
#endif

  if(pps.empty())
    return zeros(op0.size());
  else
  {
    if(use_wallace_tree)
      return wallace_tree(pps);
    if(use_carry_save)
      return comba_column_wise(pps);

    // Use multiplier-specific adder encoding
    auto saved = adder_encoding;
    adder_encoding = multiplier_adder_encoding;

    bvt product = pps.front();

    for(auto it = std::next(pps.begin()); it != pps.end(); ++it)
      product = add(product, *it);

    adder_encoding = saved;
    return product;
  }
}

bvt bv_utilst::unsigned_karatsuba_full_multiplier(
  const bvt &op0,
  const bvt &op1)
{
  // We review symbolic encoding of multiplication in context of sw
  // verification, bit width is 2^n, distinguish truncating (x mod 2^2^n) from
  // double-output-width multiplication, truncating Karatsuba is 2 truncating
  // half-width multiplication plus one double-output-width of half width, for
  // double output width Karatsuba idea is challenge to avoid width extension,
  // check Wikipedia edit history

  PRECONDITION(op0.size() == op1.size());
  const std::size_t op_size = op0.size();
  PRECONDITION(op_size > 0);
  PRECONDITION((op_size & (op_size - 1)) == 0);

  if(op_size == 1)
    return {prop.land(op0[0], op1[0]), const_literal(false)};

  const std::size_t half_op_size = op_size >> 1;

  bvt x0{op0.begin(), op0.begin() + half_op_size};
  bvt x1{op0.begin() + half_op_size, op0.end()};

  bvt y0{op1.begin(), op1.begin() + half_op_size};
  bvt y1{op1.begin() + half_op_size, op1.end()};

  bvt z0 = unsigned_karatsuba_full_multiplier(x0, y0);
  bvt z2 = unsigned_karatsuba_full_multiplier(x1, y1);

  bvt x0_sub = zero_extension(x0, half_op_size + 1);
  bvt x1_sub = zero_extension(x1, half_op_size + 1);

  bvt y0_sub = zero_extension(y0, half_op_size + 1);
  bvt y1_sub = zero_extension(y1, half_op_size + 1);

  bvt x1_minus_x0_ext = sub(x1_sub, x0_sub);
  literalt x1_minus_x0_sign = sign_bit(x1_minus_x0_ext);
  bvt x1_minus_x0_abs = absolute_value(x1_minus_x0_ext);
  x1_minus_x0_abs.pop_back();
  bvt y0_minus_y1_ext = sub(y0_sub, y1_sub);
  literalt y0_minus_y1_sign = sign_bit(y0_minus_y1_ext);
  bvt y0_minus_y1_abs = absolute_value(y0_minus_y1_ext);
  y0_minus_y1_abs.pop_back();
  bvt sub_mult =
    unsigned_karatsuba_full_multiplier(x1_minus_x0_abs, y0_minus_y1_abs);
  bvt sub_mult_ext = zero_extension(sub_mult, op_size + 1);
  bvt z1_ext = add_sub(
    add(zero_extension(z0, op_size + 1), zero_extension(z2, op_size + 1)),
    sub_mult_ext,
    prop.lxor(x1_minus_x0_sign, y0_minus_y1_sign));

  bvt z0_full = zero_extension(z0, op_size << 1);
  bvt z1_full =
    zero_extension(concatenate(zeros(half_op_size), z1_ext), op_size << 1);
  bvt z2_full = concatenate(zeros(op_size), z2);

  return add(add(z0_full, z1_full), z2_full);
}

bvt bv_utilst::unsigned_karatsuba_multiplier(const bvt &_op0, const bvt &_op1)
{
  if(_op0.size() != _op1.size())
    return unsigned_multiplier(_op0, _op1);

  const std::size_t op_size = _op0.size();
  if(op_size == 1)
    return {prop.land(_op0[0], _op1[0])};

  // Make sure we work with operands the length of which are powers of two
  const std::size_t log2 = address_bits(op_size);
  PRECONDITION(sizeof(std::size_t) * CHAR_BIT > log2);
  const std::size_t two_to_log2 = (std::size_t)1 << log2;
  bvt a = zero_extension(_op0, two_to_log2);
  bvt b = zero_extension(_op1, two_to_log2);

  const std::size_t half_op_size = two_to_log2 >> 1;

  // We split each of the operands in half and treat them as coefficients of a
  // polynomial a * 2^half_op_size + b. Straightforward polynomial
  // multiplication then yields
  // a0 * a1 * 2^op_size + (a0 * b1 + a1 * b0) * 2^half_op_size + b0 * b1
  // These would be four multiplications (the operands of which have half the
  // original bit width):
  // z0 = b0 * b1
  // z1 = a0 * b1 + a1 * b0
  // z2 = a0 * a1
  // Karatsuba's insight is that these four multiplications can be expressed
  // using just three multiplications:
  // z1 = (a0 - b0) * (b1 - a1) + z0 + z2
  //
  // Worked 4-bit example, 4-bit result:
  // abcd * efgh -> 4-bit result
  // cd * gh -> 4-bit result
  // cd * ef -> 2-bit result
  // ab * gh -> 2-bit result
  // d * h -> 2-bit result
  // c * g -> 2-bit result
  // (c - d) * (h - g) + dh + cg; use an extra sign bit for each of the
  // subtractions, and conditionally negate the product by xor-ing those sign
  // bits; dh + cg is a 2-bit addition (with possible results 0, 1, 2); the
  // product has possible values (-1, 0, 1); the final sum cannot evaluate to -1
  // as
  // * c=1, d=0, h=0, g=1 (1 * -1) implies cg=1
  // * c=0, d=1, h=1, g=0 (-1 * 1) implies dh=1
  // Therefore, after adding (dh + cg) the multiplication can safely be added
  // over just 2 bits.

  bvt x0{a.begin(), a.begin() + half_op_size};
  bvt x1{a.begin() + half_op_size, a.end()};
  bvt y0{b.begin(), b.begin() + half_op_size};
  bvt y1{b.begin() + half_op_size, b.end()};

  bvt z0 = unsigned_karatsuba_full_multiplier(x0, y0);
  bvt z1 = add(
    unsigned_karatsuba_multiplier(x1, y0),
    unsigned_karatsuba_multiplier(x0, y1));
  bvt z1_full = concatenate(zeros(half_op_size), z1);

  bvt result = add(z0, z1_full);
  CHECK_RETURN(result.size() >= op_size);
  if(result.size() > op_size)
    result.resize(op_size);
  return result;
}

bvt bv_utilst::unsigned_toom_cook_multiplier(const bvt &_op0, const bvt &_op1)
{
  PRECONDITION(_op0.size() == _op1.size());
  PRECONDITION(!_op0.empty());

  if(_op0.size() == 1)
    return {prop.land(_op0[0], _op1[0])};

  // break up _op0, _op1 in groups of at most GROUP_SIZE bits
#define GROUP_SIZE 8
  const std::size_t d_bits =
    2 * GROUP_SIZE +
    2 * address_bits((_op0.size() + GROUP_SIZE - 1) / GROUP_SIZE);
  std::vector<bvt> a, b, c_ops, d;
  for(std::size_t i = 0; i < _op0.size(); i += GROUP_SIZE)
  {
    std::size_t u = std::min(i + GROUP_SIZE, _op0.size());
    a.emplace_back(_op0.begin() + i, _op0.begin() + u);
    b.emplace_back(_op1.begin() + i, _op1.begin() + u);

    c_ops.push_back(zeros(i));
    d.push_back(prop.new_variables(d_bits));
    c_ops.back().insert(c_ops.back().end(), d.back().begin(), d.back().end());
    c_ops.back() = zero_extension(c_ops.back(), _op0.size());
  }
  for(std::size_t i = a.size(); i < 2 * a.size() - 1; ++i)
  {
    d.push_back(prop.new_variables(d_bits));
  }

  // r(0)
  bvt r_0 = d[0];
  prop.l_set_to_true(equal(
    r_0,
    unsigned_multiplier(
      zero_extension(a[0], r_0.size()), zero_extension(b[0], r_0.size()))));

  for(std::size_t j = 1; j < a.size(); ++j)
  {
    // r(2^(j-1))
    bvt r_j = zero_extension(
      d[0], std::min(_op0.size(), d[0].size() + (j - 1) * (d.size() - 1)));
    for(std::size_t i = 1; i < d.size(); ++i)
    {
      r_j = add(
        r_j,
        shift(
          zero_extension(d[i], r_j.size()), shiftt::SHIFT_LEFT, (j - 1) * i));
    }

    bvt a_even = zero_extension(a[0], r_j.size());
    for(std::size_t i = 2; i < a.size(); i += 2)
    {
      a_even = add(
        a_even,
        shift(
          zero_extension(a[i], a_even.size()),
          shiftt::SHIFT_LEFT,
          (j - 1) * i));
    }
    bvt a_odd = zero_extension(a[1], r_j.size());
    for(std::size_t i = 3; i < a.size(); i += 2)
    {
      a_odd = add(
        a_odd,
        shift(
          zero_extension(a[i], a_odd.size()),
          shiftt::SHIFT_LEFT,
          (j - 1) * (i - 1)));
    }
    bvt b_even = zero_extension(b[0], r_j.size());
    for(std::size_t i = 2; i < b.size(); i += 2)
    {
      b_even = add(
        b_even,
        shift(
          zero_extension(b[i], b_even.size()),
          shiftt::SHIFT_LEFT,
          (j - 1) * i));
    }
    bvt b_odd = zero_extension(b[1], r_j.size());
    for(std::size_t i = 3; i < b.size(); i += 2)
    {
      b_odd = add(
        b_odd,
        shift(
          zero_extension(b[i], b_odd.size()),
          shiftt::SHIFT_LEFT,
          (j - 1) * (i - 1)));
    }

    prop.l_set_to_true(equal(
      r_j,
      unsigned_multiplier(
        add(a_even, shift(a_odd, shiftt::SHIFT_LEFT, j - 1)),
        add(b_even, shift(b_odd, shiftt::SHIFT_LEFT, j - 1)))));

    // r(-2^(j-1))
    bvt r_minus_j = zero_extension(
      d[0], std::min(_op0.size(), d[0].size() + (j - 1) * (d.size() - 1)));
    for(std::size_t i = 1; i < d.size(); ++i)
    {
      if(i % 2 == 1)
      {
        r_minus_j = sub(
          r_minus_j,
          shift(
            zero_extension(d[i], r_minus_j.size()),
            shiftt::SHIFT_LEFT,
            (j - 1) * i));
      }
      else
      {
        r_minus_j = add(
          r_minus_j,
          shift(
            zero_extension(d[i], r_minus_j.size()),
            shiftt::SHIFT_LEFT,
            (j - 1) * i));
      }
    }

    prop.l_set_to_true(equal(
      r_minus_j,
      unsigned_multiplier(
        sub(a_even, shift(a_odd, shiftt::SHIFT_LEFT, j - 1)),
        sub(b_even, shift(b_odd, shiftt::SHIFT_LEFT, j - 1)))));
  }

  if(c_ops.empty())
    return zeros(_op0.size());
  else
  {
#ifdef WALLACE_TREE
    return wallace_tree(c_ops);
#elif defined(DADDA_TREE)
    return dadda_tree(c_ops);
#elif defined(COMBA)
    return comba_column_wise(c_ops);
#else
    bvt product = c_ops.front();

    for(auto it = std::next(c_ops.begin()); it != c_ops.end(); ++it)
      product = add(product, *it);

    return product;
#endif
  }
}

bvt bv_utilst::unsigned_schoenhage_strassen_multiplier(
  const bvt &a,
  const bvt &b)
{
  PRECONDITION(a.size() == b.size());

  // Running examples: we want to multiple 213 by 15 as 8- or 9-bit integers.
  // That is, we seek to multiply 11010101 (011010101) by 00001111 (000001111).
  //                              ^bit 7 ^bit 0
  // The expected result is 123 as both an 8-bit and 9-bit result (001111011).

  // We compute the result modulo a Fermat number F_m = 2^2^m + 1. The maximum
  // result when multiplying a by b (with their sizes being the same per the
  // precondition above) is 2^2*op_size - 1.
  // TODO: we don't actually need a full multiplier, a result with up to op_size
  // bits is sufficient for our purposes.
  // Hence we require 2^2^m >= 2^2*op_size, i.e., 2^m >= 2*op_size, or
  // m >= log_2(op_size) + 1.
  // For our examples m will be 4 and 5, respectively, with Fermat numbers
  // 2^16 + 1 and 2^32 + 1.
  const std::size_t m = address_bits(a.size()) + 1;
  std::cerr << "m: " << m << std::endl;

  // Extend bit width to 2^(m + 1) = op_size (rounded to next power of 2) * 4
  // For our examples, extended bit widths will be 32 and 64.
  PRECONDITION(sizeof(std::size_t) * CHAR_BIT > m + 1);
  const std::size_t two_to_m_plus_1 = (std::size_t)1 << (m + 1);
  std::cerr << "a: " << beautify(a) << std::endl;
  std::cerr << "b: " << beautify(b) << std::endl;
  bvt a_ext = zero_extension(a, two_to_m_plus_1);
  bvt b_ext = zero_extension(b, two_to_m_plus_1);

  // We need to distinguish whether m is even or odd
  // m = 2n - 1 for odd m and m = 2n -2 for even m
  // For our 8-bit inputs we have m = 4 and, therefore, n = 3.
  // For our 9-bit inputs we have m = 5 and, therefore, n = 3.
  const std::size_t n = m % 2 == 1 ? (m + 1) / 2 : m / 2 + 1;
  std::cerr << "n: " << n << std::endl;

  // For even m create 2^n (of 2^(n - 1) bits) chunks from a_ext, b_ext (for our
  // 8-bit inputs we have chunk_size = 4 with num_chunks = 8).
  // For odd m create 2^(n + 1) chunks (of 2^(n - 1) bits) from a_ext, b_ext;
  // a_0 will be bit positions 0 through to 2^(n - 1) - 1, a_{2^(n + 1) - 1}
  // will be bit positions up to 2^(m + 1) - 1.
  // For our 9-bit inputs we have chunk_size = 4 with num_chunks = 16
  const std::size_t chunk_size = (std::size_t)1 << (n - 1);
  const std::size_t num_chunks = two_to_m_plus_1 / chunk_size;
  CHECK_RETURN(
    num_chunks == m % 2 ? (std::size_t)1 << (n + 1) : (std::size_t)1 << n);
  std::cerr << "chunk_size: " << chunk_size << std::endl;
  std::cerr << "num_chunks: " << num_chunks << std::endl;
  std::cerr << "address_bits(num_chunks): " << address_bits(num_chunks)
            << std::endl;

  std::vector<bvt> a_rho, b_sigma;
  a_rho.reserve(num_chunks);
  b_sigma.reserve(num_chunks);
  for(std::size_t i = 0; i < num_chunks; ++i)
  {
    a_rho.emplace_back(
      a_ext.begin() + i * chunk_size, a_ext.begin() + (i + 1) * chunk_size);
    b_sigma.emplace_back(
      b_ext.begin() + i * chunk_size, b_ext.begin() + (i + 1) * chunk_size);
  }
  // For our example we now have
  // a_rho = [ 0101, 1101, 0000, ..., 0000 ]
  // b_sigma = [ 1111, 0000, 0000, ..., 0000 ]

  // Compute gamma_r = \sum_{i + j = r} a_i * b_j with bit width 3n + 5 with r
  // ranging from 0 to 2^(n + 2) - 1 (to 2^(n + 1) - 1 when m is even).
  // For our example this will be additions/multiplications of width 14
  // (implying that school book multiplication would be cheaper, as is the case
  // for all operand lengths below 32 bits).
  // TODO: all subsequent steps seem to be using mod 2^(n + 2) (mod 2^(n + 1)
  // when m is even), so it may be sufficient to do this over n + 2 bits instead
  // of 3n + 5.
  std::vector<bvt> gamma_tau{num_chunks * 2, zeros(3 * n + 5)};
  for(std::size_t tau = 0; tau < num_chunks * 2; ++tau)
  {
    for(std::size_t rho = tau < num_chunks ? 0 : tau - num_chunks + 1;
        rho < num_chunks && rho <= tau;
        ++rho)
    {
      const std::size_t sigma = tau - rho;
      gamma_tau[tau] = add(
        gamma_tau[tau],
        unsigned_multiplier(
          zero_extension(a_rho[rho], 3 * n + 5),
          zero_extension(b_sigma[sigma], 3 * n + 5)));
    }
  }
  // For our example we obtain
  // gamma_tau = [ 00 0000 0100 1011, 00 0000 1100 0011, 0.... ]

  // Compute c_tau over bit width n + 2 (n + 1 when m is even) as gamma_tau +
  // gamma_{tau + 2^(n + 1)} (gamma_{tau + 2^n} when m is even).
  std::vector<bvt> c_tau;
  c_tau.reserve(num_chunks);
  for(std::size_t tau = 0; tau < num_chunks; ++tau)
  {
    c_tau.push_back(add(gamma_tau[tau], gamma_tau[tau + num_chunks]));
    CHECK_RETURN(c_tau.back().size() >= address_bits(num_chunks) + 1);
    c_tau.back().resize(address_bits(num_chunks) + 1);
    std::cerr << "c_tau[" << tau << "]: " << beautify(c_tau[tau]) << std::endl;
  }
  // For our example we obtain
  // c_tau = [ 01011, 00011, 0... ]

  // Compute z_j = c_j - c_{j + 2^n} (mod 2^(n + 2)) (mod 2^(n + 1) and c_{j +
  // 2^(n - 1)} when m is even)
  std::vector<bvt> z_j;
  z_j.reserve(num_chunks / 2);
  for(std::size_t j = 0; j < num_chunks / 2; ++j)
    z_j.push_back(sub(c_tau[j], c_tau[j + num_chunks / 2]));
  // For our example we have z_j = c_tau as all elements beyond the second one
  // are zeros.

  // Compute z_j mod F_n using number-theoretic transform with omega = 2 for
  // odd m and omega = 4 for even m.
  // For our examples we have F_n = 2^2^n + 1 = 257 with 2 being a 2^(n + 1)-th
  // root of unity, i.e., 2^16 \equiv 1 (mod 257) (with 4 being a 2^n-root of
  // unity, i.e., 4^8 \equiv 1 (mod 257). The DFT table for omega = 2 would be
  // 1   1   1   1   1   1   1   1   1   1   1   1   1   1   1   1
  // 1   2   4   8  16  32  64 128  -1  -2  -4  -8 -16 -32 -64 -128
  // 1   4  16  64  -1  -4 -16 -64   1   4  16  64  -1  -4 -16 -64
  // 1   8  64  -2 -16 -128  4  32  -1  -8 -64   2  16 128  -4 -32
  // 1  16  -1 -16   1  16  -1 -16   1  16  -1 -16   1  16  -1 -16
  // 1  32  -4 -128 16  -2 -64   8  -1 -32   4 128 -16   2  64  -8
  // 1  64 -16   4  -1 -64  16  -2   1  64 -16   4  -1 -64  16  -4
  // 1 128 -64  32 -16   8  -2   2  -1 -128 64 -32  16  -8   4  -2
  // 1  -1   1  -1   1  -1   1  -1   1  -1   1  -1   1  -1   1  -1
  // 1  -2   4  -8  16 -32  64 -128 -1   2  -4   8 -16  32 -64 128
  // 1  -4  16 -64  -1   4 -16  64   1  -4  16 -64  -1   4 -16  64
  // 1  -8  64   2 -16 128   4 -32  -1   8 -64  -2  16 -128 -4  32
  // 1 -16  -1  16   1 -16  -1  16   1 -16  -1  16   1 -16  -1  16
  // 1 -32  -4 128  16   2 -64  -8  -1  32   4 -128 -16 -2  64   8
  // 1 -64 -16  -4  -1  64  16   4   1 -64 -16  -4  -1  64  16   4
  // 1 -128 -64 -32 -16 -8  -4  -2  -1 128  64  32  16   8   4   2
  // For fast NTT (less than O(n^2)) use Cooley-Tukey for NTT, then perform
  // element-wise multiplication, and finally apply Gentleman-Sande for
  // inverse NTT.

  // Addition mod F_n with overflow
  auto cyclic_add = [this](const bvt &x, const bvt &y)
  {
    PRECONDITION(x.size() == y.size());

    auto result_with_overflow = adder(x, y, const_literal(false));
    if(result_with_overflow.second.is_false())
      return result_with_overflow.first;

    return add(
      result_with_overflow.first,
      zero_extension(bvt{1, result_with_overflow.second}, x.size()));
  };

  // Compute NTT
  std::vector<bvt> a_j, b_j;
  a_j.reserve(num_chunks);
  b_j.reserve(num_chunks);
  for(std::size_t j = 0; j < num_chunks; ++j)
  {
    // All NTT steps are mod F_n, i.e., mod 2^2^n + 1, which implies we need
    // 2^(n + 1) bits to represent numbers
    a_j.push_back(zero_extension(a_rho[j], (std::size_t)1 << (n + 1)));
    b_j.push_back(zero_extension(b_sigma[j], (std::size_t)1 << (n + 1)));
  }
  // Use in-place iterative Cooley-Tukey
  std::vector<bvt> Aa, Ab;
  Aa.reserve(num_chunks);
  Ab.reserve(num_chunks);
  // In the following we use k represented as bits k_{n - 1}...k_0 and
  // j_0...j_{n - 1}, i.e., the most-significant bit of k is k_{n - 1} while the
  // MSB for j is j_0.
  for(std::size_t k = 0; k < num_chunks; ++k)
  {
    // reverse n (n - 1 if m is even) bits of k
    std::size_t j = 0;
    for(std::size_t nu = 0; nu < address_bits(num_chunks); ++nu)
    {
      j <<= 1; // the initial shift has no effect
      j |= (k & (1 << nu)) >> nu;
    }
    Aa.push_back(a_j[j]);
    Ab.push_back(b_j[j]);
  }
  for(std::size_t nu = 1; nu <= address_bits(num_chunks); ++nu)
  {
    const std::size_t bit_nu = (std::size_t)1 << (nu - 1);
    std::size_t bits_up_to_nu = 0;
    for(std::size_t i = 0; i < nu - 1; ++i)
      bits_up_to_nu |= 1 << i;

    // we only need odd ones
    for(std::size_t k = 1; k < num_chunks; k += 2)
    {
      if((k & bit_nu) == 0)
        continue;

      bvt Aa_nu_bit_is_zero = Aa[k & ~bit_nu];
      bvt Ab_nu_bit_is_zero = Ab[k & ~bit_nu];

      const std::size_t chi = (k & bits_up_to_nu)
                              << (address_bits(num_chunks) - 1 - (nu - 1));
      const std::size_t omega = m % 2 == 1 ? 2 : 4;
      const std::size_t shift_dist = chi * omega / 2;

      if(nu > 1) // no need to update even indices
      {
        Aa[k & ~bit_nu] = cyclic_add(
          Aa_nu_bit_is_zero, shift(Aa[k], shiftt::ROTATE_LEFT, shift_dist));
        Ab[k & ~bit_nu] = cyclic_add(
          Ab_nu_bit_is_zero, shift(Ab[k], shiftt::ROTATE_LEFT, shift_dist));
        std::cerr << "Aa[" << nu << "](" << (k & ~bit_nu)
                  << "): " << beautify(Aa[k & ~bit_nu]) << std::endl;
#if 0
        std::cerr << "Ab[" << nu << "](" << (k & ~bit_nu)
                  << "): " << beautify(Ab[k & ~bit_nu]) << std::endl;
#endif
      }

      // subtraction mod F_n is addition of subtrahend cyclically shifted 2^n
      // positions to the left
      const std::size_t shift_dist_for_sub = shift_dist + ((std::size_t)1 << n);
      Aa[k] = cyclic_add(
        Aa_nu_bit_is_zero,
        shift(Aa[k], shiftt::ROTATE_LEFT, shift_dist_for_sub));
      Ab[k] = cyclic_add(
        Ab_nu_bit_is_zero,
        shift(Ab[k], shiftt::ROTATE_LEFT, shift_dist_for_sub));
      std::cerr << "Aa[" << nu << "](" << k << "): " << beautify(Aa[k])
                << std::endl;
#if 0
      std::cerr << "Ab[" << nu << "](" << k << "): " << beautify(Ab[k])
                << std::endl;
#endif
    }
  }

  // Either compute u - v (if u > v), else u - v + 2^2^n + 1
  auto reduce_to_mod_F_n = [this](const bvt &x)
  {
    const std::size_t two_to_power_of_n = x.size() / 2;
    // std::cerr << "two_to_power_of_n: " << two_to_power_of_n << std::endl;
    const bvt u =
      zero_extension(bvt{x.begin(), x.begin() + two_to_power_of_n}, x.size());
    // std::cerr << "u: " << beautify(u) << std::endl;
    const bvt v =
      zero_extension(bvt{x.begin() + two_to_power_of_n, x.end()}, x.size());
    // std::cerr << "v: " << beautify(v) << std::endl;
    bvt two_to_power_of_two_to_power_of_n_plus_1 = build_constant(1, x.size());
    two_to_power_of_two_to_power_of_n_plus_1[two_to_power_of_n] =
      const_literal(true);
    const bvt u_ext = select(
      unsigned_less_than(u, v),
      add(u, two_to_power_of_two_to_power_of_n_plus_1),
      u);
    // std::cerr << "u_ext: " << beautify(u_ext) << std::endl;
    return sub(u_ext, v);
  };

  std::vector<bvt> a_hat_k{num_chunks, bvt{}}, b_hat_k{num_chunks, bvt{}};
  // Reduce by F_n
  for(std::size_t j = 1; j < num_chunks; j += 2)
  {
    a_hat_k[j] = reduce_to_mod_F_n(Aa[j]);
    std::cerr << "a_hat_k[" << j << "]: " << beautify(a_hat_k[j]) << std::endl;
    b_hat_k[j] = reduce_to_mod_F_n(Ab[j]);
    std::cerr << "b_hat_k[" << j << "]: " << beautify(b_hat_k[j]) << std::endl;
  }

  // Compute point-wise multiplication
  std::vector<bvt> c_hat_k{num_chunks, bvt{}};
  for(std::size_t j = 1; j < num_chunks; j += 2)
  {
    c_hat_k[j] = unsigned_multiplier(a_hat_k[j], b_hat_k[j]);
    std::cerr << "c_hat_k[" << j << "]: " << beautify(c_hat_k[j]) << std::endl;
  }

  // Apply inverse NTT
  for(std::size_t nu = address_bits(num_chunks) - 1; nu > 0; --nu)
  {
    const std::size_t bit_nu_plus_1 = (std::size_t)1 << nu;
    std::size_t bits_up_to_nu_plus_1 = 0;
    for(std::size_t i = 0; i < nu; ++i)
      bits_up_to_nu_plus_1 |= 1 << i;

    // we only need odd ones
    for(std::size_t k = 1; k < num_chunks; k += 2)
    {
      if((k & bit_nu_plus_1) == 0)
        continue;

      bvt c_hat_k_nu_plus_1_bit_is_zero = c_hat_k[k & ~bit_nu_plus_1];

      c_hat_k[k & ~bit_nu_plus_1] = shift(
        cyclic_add(c_hat_k_nu_plus_1_bit_is_zero, c_hat_k[k]),
        shiftt::ROTATE_RIGHT,
        1);
      std::cerr << "c_hat_k[" << nu << "](" << (k & ~bit_nu_plus_1)
                << "): " << beautify(c_hat_k[k & ~bit_nu_plus_1]) << std::endl;

      const std::size_t chi = (k & bits_up_to_nu_plus_1)
                              << (address_bits(num_chunks) - 1 - nu);
      const std::size_t omega = m % 2 == 1 ? 2 : 4;
      const std::size_t shift_dist = chi * omega / 2 + 1;
      std::cerr << "SHIFT: " << shift_dist << std::endl;

      c_hat_k[k] = shift(
        cyclic_add(
          c_hat_k_nu_plus_1_bit_is_zero,
          shift(c_hat_k[k], shiftt::ROTATE_LEFT, (std::size_t)1 << n)),
        shiftt::ROTATE_RIGHT,
        shift_dist);
      std::cerr << "c_hat_k[" << nu << "](" << k
                << "): " << beautify(c_hat_k[k]) << std::endl;
    }
  }
  // Reduce by F_n
  std::vector<bvt> z_j_mod_F_n;
  z_j_mod_F_n.reserve(num_chunks / 2);
  for(std::size_t j = 0; j < num_chunks / 2; ++j)
  {
    // reverse n - 1 (n - 2 if m is even) bits of j
    std::size_t k = 0;
    for(std::size_t nu = 0; nu < address_bits(num_chunks) - 1; ++nu)
    {
      k |= (j & (1 << nu)) >> nu;
      k <<= 1;
    }
    k |= 1;
    std::cerr << "j " << j << " maps to " << k << std::endl;
    z_j_mod_F_n.push_back(reduce_to_mod_F_n(c_hat_k[k]));
    std::cerr << "z_j_mod_F_n[" << j << "]: " << beautify(z_j_mod_F_n[j])
              << std::endl;
  }

  // Compute final coefficients as eta + delta * F_n where delta = eta - xi for
  // eta z_j and xi c_hat_k.
  for(std::size_t j = 0; j < num_chunks / 2; ++j)
  {
    bvt eta = z_j_mod_F_n[j];
    std::cerr << "eta[" << j << "]: " << beautify(eta) << std::endl;
    bvt xi = z_j[j];
    std::cerr << "xi[" << j << "]: " << beautify(xi) << std::endl;
    // TODO: couldn't we do this over just xi.size() bits instead?
    bvt delta = sub(eta, zero_extension(xi, eta.size()));
    CHECK_RETURN(delta.size() >= xi.size());
    delta.resize(xi.size());
    std::cerr << "delta[" << j << "]: " << beautify(delta) << std::endl;
    z_j[j] = add(
      zero_extension(eta, two_to_m_plus_1),
      add(
        shift(
          zero_extension(delta, two_to_m_plus_1),
          shiftt::SHIFT_LEFT,
          (std::size_t)1 << n),
        zero_extension(delta, two_to_m_plus_1)));
    std::cerr << "z_j[" << j << "]: " << beautify(z_j[j]) << std::endl;
  }

  bvt result = zeros(two_to_m_plus_1);
  for(std::size_t j = 0; j < num_chunks / 2; ++j)
  {
    if(chunk_size * j >= a.size())
      break;
    result = add(result, shift(z_j[j], shiftt::SHIFT_LEFT, chunk_size * j));
  }
  std::cerr << "result: " << beautify(result) << std::endl;
  CHECK_RETURN(result.size() >= a.size());
  result.resize(a.size());
  std::cerr << "result resized: " << beautify(result) << std::endl;

  return result;
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

      // Use multiplier-specific adder encoding
      auto saved_enc = adder_encoding;
      adder_encoding = multiplier_adder_encoding;
      product = adder_no_overflow(product, tmpop);
      adder_encoding = saved_enc;

      for(std::size_t idx=op1.size()-sum; idx<op1.size(); idx++)
        prop.l_set_to_false(prop.land(op1[idx], op0[sum]));
    }

  return product;
}

bvt bv_utilst::signed_multiplier(const bvt &op0, const bvt &op1)
{
  if(op0.empty() || op1.empty())
    return bvt();

  literalt sign0 = sign_bit(op0);
  literalt sign1 = sign_bit(op1);

  bvt neg0=cond_negate(op0, sign0);
  bvt neg1=cond_negate(op1, sign1);

#ifdef USE_KARATSUBA
  bvt result = unsigned_karatsuba_multiplier(neg0, neg1);
#elif defined(USE_TOOM_COOK)
  bvt result = unsigned_toom_cook_multiplier(neg0, neg1);
#elif defined(USE_SCHOENHAGE_STRASSEN)
  bvt result = unsigned_schoenhage_strassen_multiplier(neg0, neg1);
#else
  bvt result=unsigned_multiplier(neg0, neg1);
#endif

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
  return cond_negate(bv, sign_bit(bv));
}

bvt bv_utilst::cond_negate_no_overflow(const bvt &bv, literalt cond)
{
  prop.l_set_to_true(prop.limplies(cond, !overflow_negate(bv)));

  return cond_negate(bv, cond);
}

bvt bv_utilst::signed_multiplier_no_overflow(
  const bvt &op0,
  const bvt &op1)
{
  if(op0.empty() || op1.empty())
    return bvt();

  literalt sign0 = sign_bit(op0);
  literalt sign1 = sign_bit(op1);

  bvt neg0=cond_negate_no_overflow(op0, sign0);
  bvt neg1=cond_negate_no_overflow(op1, sign1);

  bvt result=unsigned_multiplier_no_overflow(neg0, neg1);

  prop.l_set_to_false(sign_bit(result));

  literalt result_sign=prop.lxor(sign0, sign1);

  return cond_negate_no_overflow(result, result_sign);
}

bvt bv_utilst::multiplier(
  const bvt &op0,
  const bvt &op1,
  representationt rep)
{
  // We determine the result size from the operand size, and the implementation
  // liberally swaps the operands, so we need to arrive at the same size
  // whatever the order of the operands.
  PRECONDITION(op0.size() == op1.size());

  switch(rep)
  {
  case representationt::SIGNED: return signed_multiplier(op0, op1);
#ifdef USE_KARATSUBA
  case representationt::UNSIGNED:
    return unsigned_karatsuba_multiplier(op0, op1);
#elif defined(USE_TOOM_COOK)
  case representationt::UNSIGNED:
    return unsigned_toom_cook_multiplier(op0, op1);
#elif defined(USE_SCHOENHAGE_STRASSEN)
  case representationt::UNSIGNED:
    return unsigned_schoenhage_strassen_multiplier(op0, op1);
#else
  case representationt::UNSIGNED: return unsigned_multiplier(op0, op1);
#endif
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

  literalt sign_0 = sign_bit(_op0);
  literalt sign_1 = sign_bit(_op1);

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
  res = prop.new_variables(width);
  rem = prop.new_variables(width);

  // add implications

  bvt product=
    unsigned_multiplier_no_overflow(res, op1);

  // res*op1 + rem = op0

  bvt sum = adder_no_overflow(product, rem);

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
///   to avoid significant amounts of copying these are mutable and consumed.
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

#define COMPACT_LT_OR_LE
/* Some clauses are not needed for correctness but they remove
   models (effectively setting "don't care" bits) and so may be worth
   including.*/
// #define INCLUDE_REDUNDANT_CLAUSES

literalt bv_utilst::lt_or_le(
  bool or_equal,
  const bvt &bv0,
  const bvt &bv1,
  representationt rep)
{
  PRECONDITION(bv0.size() == bv1.size());
  PRECONDITION(!bv0.empty());

#ifdef COMPACT_LT_OR_LE
  if(prop.has_set_to() && prop.cnf_handled_well())
  {
    if(rep == representationt::SIGNED)
    {
      literalt top0 = sign_bit(bv0), top1 = sign_bit(bv1);

      if(top0.is_false() && top1.is_true())
        return const_literal(false);
      else if(top0.is_true() && top1.is_false())
        return const_literal(true);

      // 1-bit signed: the sign bit is the only bit
      if(bv0.size() == 1)
      {
        if(or_equal)
          return prop.lor(top0, !top1);
        else
          return prop.land(top0, !top1);
      }

      INVARIANT(
        bv0.size() >= 2,
        "the compact signed comparison encoding requires at least two bits");
      // 1 if a compare is needed below this bit
      bvt compareBelow = prop.new_variables(bv0.size() - 1);
      size_t start = compareBelow.size() - 1;

      literalt &firstComp = compareBelow[start];
      if(top0.is_false())
        firstComp = !top1;
      else if(top0.is_true())
        firstComp = top1;
      else if(top1.is_false())
        firstComp = !top0;
      else if(top1.is_true())
        firstComp = top0;

      literalt result = prop.new_variable();

      // When comparing signs we are comparing the top bit
      // Four cases...
      prop.lcnf(top0, top1, firstComp);  // + + compare needed
      prop.lcnf(top0, !top1, !result); // + - result false and no compare needed
      prop.lcnf(!top0, top1, result); // - + result true and no compare needed
      prop.lcnf(!top0, !top1, firstComp);  // - - negated compare needed

#ifdef INCLUDE_REDUNDANT_CLAUSES
      prop.lcnf(top0, !top1, !firstComp);
      prop.lcnf(!top0,  top1, !firstComp);
#  endif

      // Determine the output
      //  \forall i .  cb[i] & -a[i] &  b[i] =>  result
      //  \forall i .  cb[i] &  a[i] & -b[i] => -result
      size_t i = start;
      do
      {
        if(compareBelow[i].is_false())
          continue;

        prop.lcnf(!compareBelow[i], bv0[i], !bv1[i], result);
        prop.lcnf(!compareBelow[i], !bv0[i], bv1[i], !result);
      } while(i-- != 0);

      // Chain the comparison bit
      //  \forall i != 0 . cb[i] &  a[i] &  b[i] => cb[i-1]
      //  \forall i != 0 . cb[i] & -a[i] & -b[i] => cb[i-1]
      for(i = start; i > 0; i--)
      {
        prop.lcnf(!compareBelow[i], !bv0[i], !bv1[i], compareBelow[i - 1]);
        prop.lcnf(!compareBelow[i], bv0[i], bv1[i], compareBelow[i - 1]);
      }

#  ifdef INCLUDE_REDUNDANT_CLAUSES
      // Optional zeroing of the comparison bit when not needed
      //  \forall i != 0 . -c[i] => -c[i-1]
      //  \forall i != 0 .  c[i] & -a[i] &  b[i] => -c[i-1]
      //  \forall i != 0 .  c[i] &  a[i] & -b[i] => -c[i-1]
      for(i = start; i > 0; i--)
      {
        prop.lcnf(compareBelow[i], !compareBelow[i - 1]);
        prop.lcnf(!compareBelow[i], bv0[i], !bv1[i], !compareBelow[i - 1]);
        prop.lcnf(!compareBelow[i], !bv0[i], bv1[i], !compareBelow[i - 1]);
      }
#  endif

      // The 'base case' of the induction is the case when they are equal
      prop.lcnf(
        !compareBelow[0], !bv0[0], !bv1[0], (or_equal) ? result : !result);
      prop.lcnf(
        !compareBelow[0], bv0[0], bv1[0], (or_equal) ? result : !result);

      return result;
    }
    else
    {
      // Unsigned is much easier
      // 1 if a compare is needed below this bit
      bvt compareBelow;
      literalt result;
      size_t start = bv0.size() - 1;

      // Determine the output
      //  \forall i .  cb[i] & -a[i] &  b[i] =>  result
      //  \forall i .  cb[i] &  a[i] & -b[i] => -result
      bool same_prefix = true;
      size_t i = start;
      do
      {
        if(same_prefix)
        {
          if(i == 0)
          {
            if(or_equal)
              return prop.lor(!bv0[0], bv1[0]);
            else
              return prop.land(!bv0[0], bv1[0]);
          }
          else if(bv0[i] == bv1[i])
            continue;
          else if(bv0[i].is_false() && bv1[i].is_true())
            return const_literal(true);
          else if(bv0[i].is_true() && bv1[i].is_false())
            return const_literal(false);
          else
          {
            same_prefix = false;
            start = i;
            compareBelow = prop.new_variables(i);
            compareBelow.push_back(const_literal(true));
            result = prop.new_variable();
          }
        }

        prop.lcnf(!compareBelow[i], bv0[i], !bv1[i], result);
        prop.lcnf(!compareBelow[i], !bv0[i], bv1[i], !result);
      } while(i-- != 0);

      // Chain the comparison bit
      //  \forall i != 0 . cb[i] &  a[i] &  b[i] => cb[i-1]
      //  \forall i != 0 . cb[i] & -a[i] & -b[i] => cb[i-1]
      for(i = start; i > 0; i--)
      {
        prop.lcnf(!compareBelow[i], !bv0[i], !bv1[i], compareBelow[i - 1]);
        prop.lcnf(!compareBelow[i], bv0[i], bv1[i], compareBelow[i - 1]);
      }

#ifdef INCLUDE_REDUNDANT_CLAUSES
      // Optional zeroing of the comparison bit when not needed
      //  \forall i != 0 . -c[i] => -c[i-1]
      //  \forall i != 0 .  c[i] & -a[i] &  b[i] => -c[i-1]
      //  \forall i != 0 .  c[i] &  a[i] & -b[i] => -c[i-1]
      for(i = start; i > 0; i--)
      {
        prop.lcnf(compareBelow[i], !compareBelow[i - 1]);
        prop.lcnf(!compareBelow[i], bv0[i], !bv1[i], !compareBelow[i - 1]);
        prop.lcnf(!compareBelow[i], !bv0[i], bv1[i], !compareBelow[i - 1]);
      }
#endif

      // The 'base case' of the induction is the case when they are equal
      prop.lcnf(
        !compareBelow[0], !bv0[0], !bv1[0], (or_equal) ? result : !result);
      prop.lcnf(
        !compareBelow[0], bv0[0], bv1[0], (or_equal) ? result : !result);

      return result;
    }
  }
  else
#endif
  {
    // A <= B  iff  there is an overflow on A-B
    literalt carry=
      carry_out(bv0, inverted(bv1), const_literal(true));

    literalt result;

    if(rep==representationt::SIGNED)
      result = prop.lxor(prop.lequal(sign_bit(bv0), sign_bit(bv1)), carry);
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
  return lt_or_le(false, op0, op1, representationt::UNSIGNED);
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
  for(const auto &literal : bv)
  {
    if(!literal.is_constant())
      return false;
  }

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

/// Symbolic implementation of popcount (count of 1 bits in a bit vector)
/// Based on the pop0 algorithm from Hacker's Delight
/// \param bv: The bit vector to count 1s in
/// \return A bit vector representing the count
bvt bv_utilst::popcount(const bvt &bv)
{
  PRECONDITION(!bv.empty());

  // Determine the result width: log2(bv.size()) + 1
  std::size_t log2 = address_bits(bv.size());
  CHECK_RETURN(log2 >= 1);

  // Start with the original bit vector
  bvt x = bv;

  // Apply the parallel bit counting algorithm from Hacker's Delight (pop0).
  // The algorithm works by summing adjacent bit groups of increasing sizes.

  // Iterate through the stages of the algorithm, doubling the field size each
  // time
  for(std::size_t stage = 0; stage < log2; ++stage)
  {
    std::size_t shift_amount = 1 << stage;     // 1, 2, 4, 8, 16, ...
    std::size_t field_size = 2 * shift_amount; // 2, 4, 8, 16, 32, ...

    // Skip if the bit vector is smaller than the field size
    if(x.size() <= shift_amount)
      break;

    // Shift the bit vector
    bvt x_shifted = shift(x, shiftt::SHIFT_LRIGHT, shift_amount);

    // Create a mask with 'shift_amount' ones followed by 'shift_amount' zeros,
    // repeated
    bvt mask;
    mask.reserve(x.size());
    for(std::size_t i = 0; i < x.size(); i++)
    {
      if((i % field_size) < shift_amount)
        mask.push_back(const_literal(true));
      else
        mask.push_back(const_literal(false));
    }

    // Apply the mask to both the original and shifted bit vectors
    bvt masked_x, masked_shifted;
    masked_x.reserve(x.size());
    masked_shifted.reserve(x.size());

    for(std::size_t i = 0; i < x.size(); i++)
    {
      masked_x.push_back(prop.land(x[i], mask[i]));
      masked_shifted.push_back(prop.land(x_shifted[i], mask[i]));
    }

    // Add the masked vectors
    x = add(masked_x, masked_shifted);
  }

  return x;
}

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BV_UTILS_H
#define CPROVER_BV_UTILS_H

#include <util/mp_arith.h>

#include <solvers/prop/prop.h>

class bv_utilst
{
public:
  bv_utilst(propt &_prop):prop(_prop) { }

  typedef enum { SIGNED, UNSIGNED } representationt;

  bvt build_constant(const mp_integer &i, unsigned width);

  bvt incrementer(const bvt &op, literalt carry_in);
  bvt inc(const bvt &op) { return incrementer(op, const_literal(true)); }
  void incrementer(bvt &op, literalt carry_in, literalt &carry_out);

  bvt negate(const bvt &op);
  bvt negate_no_overflow(const bvt &op);
  bvt absolute_value(const bvt &op);

  // returns true iff unary minus will overflow
  literalt overflow_negate(const bvt &op);

  // bit-wise negation
  bvt inverted(const bvt &op);

  literalt carry(literalt a, literalt b, literalt c);

  bvt add_sub(const bvt &op0, const bvt &op1, bool subtract);
  bvt add_sub(const bvt &op0, const bvt &op1, literalt subtract);
  bvt add_sub_no_overflow(const bvt &op0, const bvt &op1, bool subtract, representationt rep);
  bvt add(const bvt &op0, const bvt &op1) { return add_sub(op0, op1, false); }
  bvt sub(const bvt &op0, const bvt &op1) { return add_sub(op0, op1, true); }
  literalt overflow_add(const bvt &op0, const bvt &op1, representationt rep);
  literalt overflow_sub(const bvt &op0, const bvt &op1, representationt rep);
  literalt carry_out(const bvt &op0, const bvt &op1, literalt carry_in);

  typedef enum { LEFT, LRIGHT, ARIGHT } shiftt;
  bvt shift(const bvt &op, const shiftt shift, unsigned distance);
  bvt shift(const bvt &op, const shiftt shift, const bvt &distance);

  bvt unsigned_multiplier(const bvt &op0, const bvt &op1);
  bvt signed_multiplier(const bvt &op0, const bvt &op1);
  bvt multiplier(const bvt &op0, const bvt &op1, representationt rep);
  bvt multiplier_no_overflow(const bvt &op0, const bvt &op1, representationt rep);

  bvt divider(const bvt &op0, const bvt &op1,
               representationt rep)
  {
    bvt res, rem;
    divider(op0, op1, res, rem, rep);
    return res;
  }

  bvt remainder(const bvt &op0, const bvt &op1,
                representationt rep)
  {
    bvt res, rem;
    divider(op0, op1, res, rem, rep);
    return rem;
  }

  void divider(const bvt &op0, const bvt &op1,
               bvt &res, bvt &rem, representationt rep);

  void signed_divider(const bvt &op0, const bvt &op1,
                      bvt &res, bvt &rem);

  void unsigned_divider(const bvt &op0, const bvt &op1,
                        bvt &res, bvt &rem);

  literalt equal(const bvt &op0, const bvt &op1);

  literalt is_zero(const bvt &op)
  { return prop.lnot(prop.lor(op)); }

  literalt is_not_zero(const bvt &op)
  { return prop.lor(op); }

  literalt is_one(const bvt &op);

  literalt is_all_ones(const bvt &op)
  { return prop.land(op); }

  literalt lt_or_le(bool or_equal,
                    const bvt &bv0,
                    const bvt &bv1,
                    representationt rep);

  literalt unsigned_less_than(const bvt &bv0, const bvt &bv1);
  literalt signed_less_than(const bvt &bv0, const bvt &bv1);

  bool is_constant(const bvt &bv);

  bvt extension(const bvt &bv, unsigned new_size, representationt rep);

  bvt sign_extension(const bvt &bv, unsigned new_size)
  {
    return extension(bv, new_size, SIGNED);
  }

  bvt zero_extension(const bvt &bv, unsigned new_size)
  {
    return extension(bv, new_size, UNSIGNED);
  }

  bvt zeros(unsigned new_size) const
  {
    bvt result;
    result.resize(new_size, const_literal(false));
    return result;
  }
  
  void set_equal(const bvt &a, const bvt &b);

  // if cond holds, a has to be equal to b
  void cond_implies_equal(literalt cond, const bvt &a, const bvt &b);

  bvt cond_negate(const bvt &bv, const literalt cond);

  bvt select(literalt s, const bvt &a, const bvt &b);

  // computes a[last:first]  
  bvt extract(const bvt &a, unsigned first, unsigned last) const;

  // put a and b together, where a comes first (lower indices)
  bvt concatenate(const bvt &a, const bvt &b) const;

protected:
  propt &prop;

  void adder(bvt &sum, const bvt &op,
             literalt carry_in, literalt &carry_out);

  void adder_no_overflow(
    bvt &sum,
    const bvt &op,
    bool subtract,
    representationt rep);

  void adder_no_overflow(bvt &sum, const bvt &op);

  bvt unsigned_multiplier_no_overflow(
    const bvt &op0, const bvt &op1);

  bvt signed_multiplier_no_overflow(
    const bvt &op0, const bvt &op1);

  bvt cond_negate_no_overflow(const bvt &bv, const literalt cond);
};

#endif

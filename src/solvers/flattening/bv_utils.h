/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BV_UTILS_H
#define CPROVER_SOLVERS_FLATTENING_BV_UTILS_H

#include <util/mp_arith.h>

#include <solvers/prop/prop.h>

// Shares variables between var == const tests for registered variables.
// Gives ~15% memory savings on some programs using constant arrays
// but seems to give a run-time penalty.
// #define COMPACT_EQUAL_CONST


class bv_utilst
{
public:
  explicit bv_utilst(propt &_prop):prop(_prop) { }

  enum class representationt { SIGNED, UNSIGNED };

  static bvt build_constant(const mp_integer &i, std::size_t width);

  bvt incrementer(const bvt &op, literalt carry_in);
  bvt inc(const bvt &op) { return incrementer(op, const_literal(true)); }
  void incrementer(bvt &op, literalt carry_in, literalt &carry_out);

  bvt negate(const bvt &op);
  bvt negate_no_overflow(const bvt &op);
  bvt absolute_value(const bvt &op);

  // returns true iff unary minus will overflow
  literalt overflow_negate(const bvt &op);

  // bit-wise negation
  static bvt inverted(const bvt &op);

  literalt full_adder(
    const literalt a,
    const literalt b,
    const literalt carry_in,
    literalt &carry_out);
  literalt carry(literalt a, literalt b, literalt c);

  bvt add_sub(const bvt &op0, const bvt &op1, bool subtract);
  bvt add_sub(const bvt &op0, const bvt &op1, literalt subtract);
  bvt add_sub_no_overflow(
    const bvt &op0,
    const bvt &op1,
    bool subtract,
    representationt rep);
  bvt saturating_add_sub(
    const bvt &op0,
    const bvt &op1,
    bool subtract,
    representationt rep);

  bvt add(const bvt &op0, const bvt &op1) { return add_sub(op0, op1, false); }
  bvt sub(const bvt &op0, const bvt &op1) { return add_sub(op0, op1, true); }

  literalt overflow_add(const bvt &op0, const bvt &op1, representationt rep);
  literalt overflow_sub(const bvt &op0, const bvt &op1, representationt rep);
  literalt carry_out(const bvt &op0, const bvt &op1, literalt carry_in);

  enum class shiftt
  {
    SHIFT_LEFT, SHIFT_LRIGHT, SHIFT_ARIGHT, ROTATE_LEFT, ROTATE_RIGHT
  };

  static bvt shift(const bvt &op, const shiftt shift, std::size_t distance);
  bvt shift(const bvt &op, const shiftt shift, const bvt &distance);

  bvt unsigned_multiplier(const bvt &op0, const bvt &op1);
  bvt signed_multiplier(const bvt &op0, const bvt &op1);
  bvt multiplier(const bvt &op0, const bvt &op1, representationt rep);
  bvt multiplier_no_overflow(
    const bvt &op0,
    const bvt &op1,
    representationt rep);

  bvt divider(const bvt &op0, const bvt &op1, representationt rep)
  {
    bvt res, rem;
    divider(op0, op1, res, rem, rep);
    return res;
  }

  bvt remainder(const bvt &op0, const bvt &op1, representationt rep)
  {
    bvt res, rem;
    divider(op0, op1, res, rem, rep);
    return rem;
  }

  void divider(
    const bvt &op0,
    const bvt &op1,
    bvt &res,
    bvt &rem,
    representationt rep);

  void signed_divider(
    const bvt &op0,
    const bvt &op1,
    bvt &res,
    bvt &rem);

  void unsigned_divider(
    const bvt &op0,
    const bvt &op1,
    bvt &res,
    bvt &rem);

  #ifdef COMPACT_EQUAL_CONST
  typedef std::set<bvt> equal_const_registeredt;
  equal_const_registeredt equal_const_registered;
  void equal_const_register(const bvt &var);

  typedef std::pair<bvt, bvt> var_constant_pairt;
  typedef std::map<var_constant_pairt, literalt> equal_const_cachet;
  equal_const_cachet equal_const_cache;

  literalt equal_const_rec(bvt &var, bvt &constant);
  literalt equal_const(const bvt &var, const bvt &constant);
  #endif


  literalt equal(const bvt &op0, const bvt &op1);

  static inline literalt sign_bit(const bvt &op)
  {
    return op[op.size()-1];
  }

  literalt is_zero(const bvt &op)
  { return !prop.lor(op); }

  literalt is_not_zero(const bvt &op)
  { return prop.lor(op); }

  literalt is_int_min(const bvt &op)
  {
    bvt tmp=op;
    tmp[tmp.size()-1]=!tmp[tmp.size()-1];
    return is_zero(tmp);
  }

  literalt is_one(const bvt &op);

  literalt is_all_ones(const bvt &op)
  { return prop.land(op); }

  literalt lt_or_le(
    bool or_equal,
    const bvt &bv0,
    const bvt &bv1,
    representationt rep);

  // id is one of ID_lt, le, gt, ge, equal, notequal
  literalt rel(
    const bvt &bv0,
    irep_idt id,
    const bvt &bv1,
    representationt rep);

  literalt unsigned_less_than(const bvt &bv0, const bvt &bv1);
  literalt signed_less_than(const bvt &bv0, const bvt &bv1);

  static bool is_constant(const bvt &bv);

  static bvt
  extension(const bvt &bv, std::size_t new_size, representationt rep);

  bvt sign_extension(const bvt &bv, std::size_t new_size)
  {
    return extension(bv, new_size, representationt::SIGNED);
  }

  bvt zero_extension(const bvt &bv, std::size_t new_size)
  {
    return extension(bv, new_size, representationt::UNSIGNED);
  }

  bvt zeros(std::size_t new_size) const
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
  static bvt extract(const bvt &a, std::size_t first, std::size_t last);

  // extracts the n most significant bits
  static bvt extract_msb(const bvt &a, std::size_t n);

  // extracts the n least significant bits
  static bvt extract_lsb(const bvt &a, std::size_t n);

  // put a and b together, where a comes first (lower indices)
  static bvt concatenate(const bvt &a, const bvt &b);

  literalt verilog_bv_has_x_or_z(const bvt &);
  static bvt verilog_bv_normal_bits(const bvt &);

protected:
  propt &prop;

  void adder(
    bvt &sum,
    const bvt &op,
    literalt carry_in,
    literalt &carry_out);

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

  bvt wallace_tree(const std::vector<bvt> &pps);
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_UTILS_H

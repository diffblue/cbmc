/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

// REFINE_MULT_MODE selects the multiplication refinement strategy:
//   0 = original (full multiplier on first spurious result)
//   1 = assumption-gated (narrow multiplier first, then full)
//   2 = Karatsuba polynomial (k=2, 3 evaluation points, then full)
//   3 = Toom-Cook polynomial (k=n/4, evaluation at 0 and 1, then full)
//   4 = Beame-Liew adaptive strip (narrow multiplier, k grows
//       with highest spurious-bit position; falls back to full)
// Default is 1 (assumption-gated) as it gives the best overall performance.
#ifndef REFINE_MULT_MODE
#define REFINE_MULT_MODE 1
#endif

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/bv_arithmetic.h>
#include <util/expr_util.h>
#include <util/floatbv_expr.h>
#include <util/ieee_float.h>

#include <solvers/floatbv/float_utils.h>
#include <solvers/prop/literal_expr.h>

#include "bv_refinement.h"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <map>
#include <variant>

// Parameters
#define MAX_INTEGER_UNDERAPPROX 3
#define MAX_FLOAT_UNDERAPPROX 10

void bv_refinementt::approximationt::add_over_assumption(literalt l)
{
  // if it's a constant already, give up
  if(!l.is_constant())
    over_assumptions.push_back(literal_exprt(l));
}

void bv_refinementt::approximationt::add_under_assumption(literalt l)
{
  // if it's a constant already, give up
  if(!l.is_constant())
    under_assumptions.push_back(literal_exprt(l));
}

bvt bv_refinementt::convert_floatbv_op(const ieee_float_op_exprt &expr)
{
  if(!config_.refine_arithmetic)
    return SUB::convert_floatbv_op(expr);

  if(expr.type().id() != ID_floatbv)
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

  const typet &type = expr.type();

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

    // Karatsuba-style setup (only for REFINE_MULT_MODE 2)
#if REFINE_MULT_MODE == 2
    // Split operands into two halves and create
    // 3 non-deterministic coefficient variables d[0], d[1], d[2].
    // Result = d[0] + d[1] * 2^half + d[2] * 2^(2*half) (mod 2^n)
    // Evaluation points constrain them:
    //   r(0):   d[0] = a_lo * b_lo
    //   r(inf): d[2] = a_hi * b_hi
    //   r(1):   d[0]+d[1]+d[2] = (a_lo+a_hi) * (b_lo+b_hi)
    const std::size_t n = a.op0_bv.size();
    const std::size_t half = n / 2;
    if(half >= 4)
    {
      // d_bits: wide enough for half*half product
      const std::size_t d_bits = n + 2;

      // Create 3 non-deterministic coefficient variables
      bvt d0 = prop.new_variables(d_bits);
      bvt d1 = prop.new_variables(d_bits);
      bvt d2 = prop.new_variables(d_bits);

      // Constrain: result = d[0] + d[1]<<half + d[2]<<(2*half) mod 2^n
      bvt reconstructed = bv_utils.zero_extension(d0, n);
      reconstructed = bv_utils.add(
        reconstructed,
        bv_utils.shift(
          bv_utils.zero_extension(d1, n),
          bv_utilst::shiftt::SHIFT_LEFT,
          half));
      if(2 * half < n)
      {
        reconstructed = bv_utils.add(
          reconstructed,
          bv_utils.shift(
            bv_utils.zero_extension(d2, n),
            bv_utilst::shiftt::SHIFT_LEFT,
            2 * half));
      }
      bv_utils.set_equal(reconstructed, a.result_bv);

      // Store d0, d1, d2 in op2_bv for refinement
      a.op2_bv.clear();
      a.op2_bv.insert(a.op2_bv.end(), d0.begin(), d0.end());
      a.op2_bv.insert(a.op2_bv.end(), d1.begin(), d1.end());
      a.op2_bv.insert(a.op2_bv.end(), d2.begin(), d2.end());
      a.no_operands = 3; // signal that Karatsuba refinement is active
    }
#endif // REFINE_MULT_MODE == 2
#if REFINE_MULT_MODE == 3
    // Toom-Cook setup: split into 4-bit chunks, create 2k-1 non-det
    // coefficients. Result = sum(d[i] * 2^(i*chunk)) mod 2^n.
    const std::size_t n = a.op0_bv.size();
    const std::size_t chunk = 4;
    if(n > chunk)
    {
      const std::size_t num_a_chunks = (n + chunk - 1) / chunk;
      const std::size_t num_d = 2 * num_a_chunks - 1;
      const std::size_t d_bits = 2 * chunk + address_bits(num_a_chunks);

      std::vector<bvt> d_coeffs;
      d_coeffs.reserve(num_d);
      for(std::size_t i = 0; i < num_d; ++i)
        d_coeffs.push_back(prop.new_variables(d_bits));

      bvt reconstructed = bv_utils.zeros(n);
      for(std::size_t i = 0; i < num_d; ++i)
      {
        std::size_t shift_amt = i * chunk;
        if(shift_amt >= n)
          break;
        bvt shifted = bv_utils.zero_extension(d_coeffs[i], n);
        shifted = bv_utils.shift(
          shifted, bv_utilst::shiftt::SHIFT_LEFT, shift_amt);
        reconstructed = bv_utils.add(reconstructed, shifted);
      }
      bv_utils.set_equal(reconstructed, a.result_bv);

      a.op2_bv.clear();
      for(const auto &d : d_coeffs)
        a.op2_bv.insert(a.op2_bv.end(), d.begin(), d.end());
      a.no_operands = 3;
    }
#endif // REFINE_MULT_MODE == 3
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
  // see if the satisfying assignment is spurious in any way

  const typet &type = a.expr.type();

  if(type.id()==ID_floatbv)
  {
    const auto &float_op = to_ieee_float_op_expr(a.expr);

    if(a.over_state==MAX_STATE)
      return;

    // get actual rounding mode
    constant_exprt rounding_mode_expr =
      to_constant_expr(get(float_op.rounding_mode()));
    const std::size_t rounding_mode_int =
      numeric_cast_v<std::size_t>(rounding_mode_expr);
    ieee_floatt::rounding_modet rounding_mode =
      (ieee_floatt::rounding_modet)rounding_mode_int;

    ieee_float_spect spec(to_floatbv_type(type));
    ieee_floatt o0(spec, rounding_mode), o1(spec, rounding_mode);

    o0.unpack(a.op0_value);
    o1.unpack(a.op1_value);

    ieee_floatt result = o0;

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

    log.debug() << "S1: " << o0 << " " << a.expr.id() << " " << o1
                << " != " << rr << messaget::eom;
    log.debug() << "S2: " << integer2binary(a.op0_value, spec.width()) << " "
                << a.expr.id() << " "
                << integer2binary(a.op1_value, spec.width())
                << "!=" << integer2binary(a.result_value, spec.width())
                << messaget::eom;
    log.debug() << "S3: " << integer2binary(a.op0_value, spec.width()) << " "
                << a.expr.id() << " "
                << integer2binary(a.op1_value, spec.width())
                << "==" << integer2binary(result.pack(), spec.width())
                << messaget::eom;
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
      a.expr.operands().size() == 2, "all (un)signedbv typed exprs are binary");

    // already full interpretation?
#if REFINE_MULT_MODE == 0
    if(a.over_state > 0)
      return;
#elif REFINE_MULT_MODE == 1
    if(a.over_state > 1)
      return;
#elif REFINE_MULT_MODE == 4
    // Mode 4 may need many strips; bound by output bit-width.
    // The MAX_STATE check is later in the function as a safety net.
    if(a.over_state >= a.op0_bv.size() + 1)
      return;
#else // REFINE_MULT_MODE == 2 or 3
    if(a.over_state > 3)
      return;
#endif

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

    if(o0.pack()==a.result_value &&
#if REFINE_MULT_MODE == 0
       true
#elif REFINE_MULT_MODE == 1
       a.over_state > 0
#elif REFINE_MULT_MODE == 4
      // For Mode 4, any state is fine if the model is consistent.
      true
#else // mode 2 or 3
       a.over_state > 2
#endif
    )
      return;

    auto rep = a.expr.type().id() == ID_signedbv
                 ? bv_utilst::representationt::SIGNED
                 : bv_utilst::representationt::UNSIGNED;

    if(false) {} // placeholder for #if chain
#if REFINE_MULT_MODE == 2
    else if(a.expr.id() == ID_mult && a.no_operands == 3 && a.over_state == 0)
    {
      // Karatsuba r(0): d[0] = a_lo * b_lo
      const std::size_t n = a.op0_bv.size();
      const std::size_t half = n / 2;
      const std::size_t d_bits = n + 2;

      bvt d0(a.op2_bv.begin(), a.op2_bv.begin() + d_bits);
      bvt a_lo(a.op0_bv.begin(), a.op0_bv.begin() + half);
      bvt b_lo(a.op1_bv.begin(), a.op1_bv.begin() + half);

      bvt prod = bv_utils.unsigned_multiplier(
        bv_utils.zero_extension(a_lo, d_bits),
        bv_utils.zero_extension(b_lo, d_bits));
      bv_utils.set_equal(d0, prod);
    }
    else if(a.expr.id() == ID_mult && a.no_operands == 3 && a.over_state == 1)
    {
      // Karatsuba r(inf): d[2] = a_hi * b_hi
      const std::size_t n = a.op0_bv.size();
      const std::size_t half = n / 2;
      const std::size_t d_bits = n + 2;

      bvt d2(a.op2_bv.begin() + 2 * d_bits,
             a.op2_bv.begin() + 3 * d_bits);
      bvt a_hi(a.op0_bv.begin() + half, a.op0_bv.end());
      bvt b_hi(a.op1_bv.begin() + half, a.op1_bv.end());

      bvt prod = bv_utils.unsigned_multiplier(
        bv_utils.zero_extension(a_hi, d_bits),
        bv_utils.zero_extension(b_hi, d_bits));
      bv_utils.set_equal(d2, prod);
    }
    else if(a.expr.id() == ID_mult && a.no_operands == 3 && a.over_state == 2)
    {
      // Karatsuba r(1): d[0]+d[1]+d[2] = (a_lo+a_hi) * (b_lo+b_hi)
      const std::size_t n = a.op0_bv.size();
      const std::size_t half = n / 2;
      const std::size_t d_bits = n + 2;
      const std::size_t eval_bits = d_bits + 2;

      bvt d0(a.op2_bv.begin(), a.op2_bv.begin() + d_bits);
      bvt d1(a.op2_bv.begin() + d_bits, a.op2_bv.begin() + 2 * d_bits);
      bvt d2(a.op2_bv.begin() + 2 * d_bits, a.op2_bv.begin() + 3 * d_bits);

      bvt d_sum = bv_utils.add(
        bv_utils.zero_extension(d0, eval_bits),
        bv_utils.add(
          bv_utils.zero_extension(d1, eval_bits),
          bv_utils.zero_extension(d2, eval_bits)));

      bvt a_lo(a.op0_bv.begin(), a.op0_bv.begin() + half);
      bvt a_hi(a.op0_bv.begin() + half, a.op0_bv.end());
      bvt b_lo(a.op1_bv.begin(), a.op1_bv.begin() + half);
      bvt b_hi(a.op1_bv.begin() + half, a.op1_bv.end());

      bvt a_sum = bv_utils.add(
        bv_utils.zero_extension(a_lo, eval_bits),
        bv_utils.zero_extension(a_hi, eval_bits));
      bvt b_sum = bv_utils.add(
        bv_utils.zero_extension(b_lo, eval_bits),
        bv_utils.zero_extension(b_hi, eval_bits));

      bvt prod = bv_utils.unsigned_multiplier(a_sum, b_sum);
      bv_utils.set_equal(
        bv_utils.zero_extension(d_sum, prod.size()), prod);
    }
#endif // REFINE_MULT_MODE == 2
#if REFINE_MULT_MODE == 3
    else if(a.expr.id() == ID_mult && a.no_operands == 3 && a.over_state == 0)
    {
      // Toom-Cook r(0): d[0] = a[0] * b[0]
      const std::size_t n = a.op0_bv.size();
      const std::size_t chunk = 4;
      const std::size_t num_a_chunks = (n + chunk - 1) / chunk;
      const std::size_t d_bits = 2 * chunk + address_bits(num_a_chunks);

      bvt d0(a.op2_bv.begin(), a.op2_bv.begin() + d_bits);
      bvt a0(a.op0_bv.begin(),
             a.op0_bv.begin() + std::min(chunk, n));
      bvt b0(a.op1_bv.begin(),
             a.op1_bv.begin() + std::min(chunk, n));

      bvt prod = bv_utils.unsigned_multiplier(
        bv_utils.zero_extension(a0, d_bits),
        bv_utils.zero_extension(b0, d_bits));
      bv_utils.set_equal(d0, prod);
    }
    else if(a.expr.id() == ID_mult && a.no_operands == 3 && a.over_state == 1)
    {
      // Toom-Cook r(1): sum(d[i]) = sum(a_chunks) * sum(b_chunks)
      const std::size_t n = a.op0_bv.size();
      const std::size_t chunk = 4;
      const std::size_t num_a_chunks = (n + chunk - 1) / chunk;
      const std::size_t num_d = 2 * num_a_chunks - 1;
      const std::size_t d_bits = 2 * chunk + address_bits(num_a_chunks);
      const std::size_t eval_bits = d_bits + address_bits(num_d);

      bvt a_sum = bv_utils.zeros(eval_bits);
      bvt b_sum = bv_utils.zeros(eval_bits);
      for(std::size_t i = 0; i < num_a_chunks; ++i)
      {
        std::size_t lo = i * chunk;
        std::size_t hi = std::min(lo + chunk, n);
        bvt ai(a.op0_bv.begin() + lo, a.op0_bv.begin() + hi);
        bvt bi(a.op1_bv.begin() + lo, a.op1_bv.begin() + hi);
        a_sum = bv_utils.add(a_sum, bv_utils.zero_extension(ai, eval_bits));
        b_sum = bv_utils.add(b_sum, bv_utils.zero_extension(bi, eval_bits));
      }

      bvt d_sum = bv_utils.zeros(eval_bits);
      for(std::size_t i = 0; i < num_d; ++i)
      {
        bvt di(a.op2_bv.begin() + i * d_bits,
               a.op2_bv.begin() + (i + 1) * d_bits);
        d_sum = bv_utils.add(d_sum, bv_utils.zero_extension(di, eval_bits));
      }

      bvt prod = bv_utils.unsigned_multiplier(a_sum, b_sum);
      bv_utils.set_equal(
        bv_utils.zero_extension(d_sum, prod.size()), prod);
    }
#endif // REFINE_MULT_MODE == 3
#if REFINE_MULT_MODE == 4
    else if(a.expr.id() == ID_mult)
    {
      // Beame-Liew adaptive-prefix refinement.
      //
      // On a spurious counterexample, find the highest output-bit
      // position j where the true product (o0.pack() * o1.pack()) and
      // the model value (a.result_value) disagree. Constrain
      // result_bv[0..j] to equal the low j+1 bits of a width-n
      // multiplier of zero-extended (j+1)-bit operands.
      //
      // This is the simpler half of Beame and Liew's strip idea:
      // the constraint is anchored at bit 0 (no free carry-in), so
      // it is equivalent to a "narrow multiplier of width j+1" rather
      // than a true sliding window. A windowed-strip variant with a
      // fresh carry-in vector at column lo was implemented and tested
      // (commit history); however, a strip on a single multiplier is
      // underconstrained — its free carry-in admits many spurious
      // outputs. Beame-Liew's strip technique relies on coupling via
      // an equality constraint between two multipliers (the proof's
      // diff-variable structure), which `--refine-arithmetic` does
      // not inherently expose. So the windowed strip alone caused
      // many small refinements to converge slowly; the prefix
      // version below performs comparably to Mode 1.
      //
      // Once the spurious bit is in the high half of the multiplier
      // we fall back to the full multiplier, to avoid stacking
      // near-full prefix multipliers across multiple refinement
      // rounds.

      const std::size_t n = a.op0_bv.size();

      // Find highest mismatching output bit between true product and model.
      const mp_integer true_prod = o0.pack();
      std::size_t spurious_bit = 0;
      bool any_mismatch = false;
      for(std::size_t i = 0; i < n; ++i)
      {
        const mp_integer two{2};
        const bool true_bit =
          (true_prod >> mp_integer(static_cast<unsigned>(i))) % two != 0;
        const bool model_bit =
          (a.result_value >> mp_integer(static_cast<unsigned>(i))) % two != 0;
        if(true_bit != model_bit)
        {
          spurious_bit = i;
          any_mismatch = true;
        }
      }

      if(!any_mismatch)
      {
        a.over_assumptions.clear();
        bv_utils.set_equal(
          bv_utils.multiplier(a.op0_bv, a.op1_bv, rep), a.result_bv);
      }
      else
      {
        const std::size_t k = std::min(spurious_bit + 1, n);

        // If the prefix would cover most of the multiplier anyway,
        // emit the full multiplier directly. This avoids stacking
        // near-full prefix multipliers across multiple spurious-
        // counterexample refinements.
        if(k * 2 >= n)
        {
          a.over_assumptions.clear();
          bv_utils.set_equal(
            bv_utils.multiplier(a.op0_bv, a.op1_bv, rep), a.result_bv);
        }
        else
        {
          // Build a width-n multiplier on operand inputs zero-extended
          // from their k LSBs, and constrain result_bv[0..k-1] to
          // equal the low k bits.
          bvt a_low(a.op0_bv.begin(), a.op0_bv.begin() + k);
          bvt b_low(a.op1_bv.begin(), a.op1_bv.begin() + k);
          bvt r_approx = bv_utils.multiplier(
            bv_utils.zero_extension(a_low, n),
            bv_utils.zero_extension(b_low, n),
            rep);

          for(std::size_t i = 0; i < k && i < r_approx.size(); ++i)
          {
            prop.lcnf(!a.result_bv[i], r_approx[i]);
            prop.lcnf(a.result_bv[i], !r_approx[i]);
          }
        }
      }
    }
#endif // REFINE_MULT_MODE == 4
#if REFINE_MULT_MODE == 1
    else if(a.expr.id() == ID_mult && a.over_state == 0)
    {
      // Assumption-gated: narrow multiplier first
      const std::size_t n = a.op0_bv.size();
      const std::size_t k = std::min(std::size_t(4), n);

      if(k < n)
      {
        a.over_assumptions.clear();
        bvt a_low(a.op0_bv.begin(), a.op0_bv.begin() + k);
        bvt b_low(a.op1_bv.begin(), a.op1_bv.begin() + k);
        bvt r_approx = bv_utils.multiplier(
          bv_utils.zero_extension(a_low, n),
          bv_utils.zero_extension(b_low, n),
          rep);

        literalt gate = prop.new_variable();
        // Only constrain the low k bits — leave high bits free.
        // This is an over-approximation: the low bits are exact,
        // the high bits can take any value.
        for(std::size_t i = 0; i < k && i < r_approx.size(); ++i)
        {
          prop.lcnf(!gate, !a.result_bv[i], r_approx[i]);
          prop.lcnf(!gate, a.result_bv[i], !r_approx[i]);
        }
        a.add_over_assumption(gate);
      }
      else
      {
        bv_utils.set_equal(
          bv_utils.multiplier(a.op0_bv, a.op1_bv, rep), a.result_bv);
      }
    }
#endif // REFINE_MULT_MODE == 1
    else if(a.over_state <= 3)
    {
      // Full interpretation (fallback for all modes, also div/mod)
      a.over_assumptions.clear();

      bvt r;
      if(a.expr.id() == ID_mult)
        r = bv_utils.multiplier(a.op0_bv, a.op1_bv, rep);
      else if(a.expr.id() == ID_div)
        r = bv_utils.divider(a.op0_bv, a.op1_bv, rep);
      else if(a.expr.id() == ID_mod)
        r = bv_utils.remainder(a.op0_bv, a.op1_bv, rep);
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

  log.status() << "Found spurious '" << a.as_string() << "' (state "
               << a.over_state << ")" << messaget::eom;

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

  log.status() << "Found assumption for '" << a.as_string()
               << "' in proof (state " << a.under_state << ")" << messaget::eom;

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
  {
    if(prop.is_in_conflict(
         to_literal_expr(a.under_assumptions[i]).get_literal()))
    {
      return true;
    }
  }

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
    a.op0_bv = convert_bv(to_unary_expr(expr).op());
    set_frozen(a.op0_bv);
  }
  else if(a.no_operands==2)
  {
    a.op0_bv = convert_bv(to_binary_expr(expr).op0());
    a.op1_bv = convert_bv(to_binary_expr(expr).op1());
    set_frozen(a.op0_bv);
    set_frozen(a.op1_bv);
  }
  else if(a.no_operands==3)
  {
    a.op0_bv = convert_bv(to_multi_ary_expr(expr).op0());
    a.op1_bv = convert_bv(to_multi_ary_expr(expr).op1());
    a.op2_bv = convert_bv(to_multi_ary_expr(expr).op2());
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

/// Identify approximations that must produce equal results by algebraic
/// identity (commutativity and associativity of bit-vector
/// multiplication). For each detected pair, assert that their
/// bit-vector results are equal.
///
/// We compute a flat multiset of "leaf" factors per multiplication
/// approximation. Operand vectors that match the result_bv of another
/// multiplication approximation are recursively expanded; this lets
/// us see through opaque computations that replaced an expression
/// with a fresh variable. For example, with code like
///   ab = store((uint64_t)a * (uint64_t)b);
///   left = ab * (uint64_t)c;
/// the SSA flow makes `left.op0 = ab_var` (a symbol) at the expression
/// level, but the bit-vector `ab_var.bv` is the result_bv of the
/// `a*b` approximation. We recover this link via BV identity.
///
/// Two multiplications with the same flat factor multiset must
/// produce equal bit-vector results (mod 2^n) because integer
/// multiplication is commutative and associative.
///
/// This catches cases where CBMC's expression-level simplifier could
/// not see the equality (multiplication results flowing through
/// opaque function calls, array stores, pointer dereferences, type
/// casts). The asserted equality is sound and constant-size (n
/// equality clauses per pair).
///
/// Future work: emit Beame-Liew-style strip lemmas alongside the
/// equality to give the SAT solver a polynomial-size proof witness
/// for the equality, useful when the equality is propagated through
/// further opaque computation.
void bv_refinementt::detect_algebraic_pairs()
{
  if(!config_.refine_arithmetic)
    return;

  // Allow disabling pair detection at runtime for benchmarking/A-B
  // comparison (CBMC_DISABLE_REFINE_PAIR_DETECTION=1).
  if(const char *env = std::getenv("CBMC_DISABLE_REFINE_PAIR_DETECTION");
     env != nullptr && env[0] != '\0' && env[0] != '0')
    return;

  // Map result_bv -> approximation iterator, for BV-level operand
  // resolution.
  std::map<bvt, approximationt *> result_bv_index;
  for(auto &a : approximations)
  {
    if(a.expr.id() != ID_mult || a.expr.operands().size() != 2)
      continue;
    const typet &t = a.expr.type();
    if(t.id() != ID_unsignedbv && t.id() != ID_signedbv)
      continue;
    result_bv_index.emplace(a.result_bv, &a);
  }

  // Compute a flat multiset of leaf factors per multiplication
  // approximation. Recurses through:
  //  (1) mult sub-expressions: mult(a, b)'s factors are factors(a) ++ factors(b);
  //  (2) operand BVs that match another approximation's result_bv.
  // The result is a sorted vector of "factors". A factor is either an
  // approximation pointer (for mults whose result_bv we resolved
  // through), or an operand bit-vector (for unresolved leaves —
  // typically symbol references). Comparing leaves at the BV level
  // catches cases where the same value reaches two multiplications
  // through differently-named SSA variables (e.g. inlined function
  // parameters).
  using factor_kind = std::variant<bvt, std::size_t>;
  std::function<void(approximationt *, std::vector<factor_kind> &)>
    flatten_mult;
  flatten_mult = [&](approximationt *m, std::vector<factor_kind> &out)
  {
    auto add_operand = [&](const exprt &op_expr, const bvt &op_bv)
    {
      // Try to resolve operand as another mult approximation via BV.
      auto it = result_bv_index.find(op_bv);
      if(it != result_bv_index.end() && it->second != m)
      {
        flatten_mult(it->second, out);
        return;
      }
      // Else: try to flatten the expression itself if it is mult(.,.).
      if(op_expr.id() == ID_mult && op_expr.operands().size() == 2)
      {
        // Best-effort: assume the operand expr's bit-blasting is the
        // standard one. We can't easily look up the resulting bv
        // here, so just flatten the expression syntactically by
        // emitting placeholder leaves identified by the operand bv
        // of each sub-leaf. Without per-sub-expression bvs, fall
        // back to a conservative leaf using the entire op_bv.
        // (This case is uncommon: it only triggers when a mult
        // operand expression contains a nested mult that did not
        // produce its own approximation, e.g. constant-folded
        // sub-products, which are rare under refine_arithmetic.)
        out.push_back(op_bv);
        return;
      }
      // Leaf identified by its bit-vector (catches differently-named
      // SSA variables with the same bit-blasted bv).
      out.push_back(op_bv);
    };

    add_operand(to_binary_expr(m->expr).op0(), m->op0_bv);
    add_operand(to_binary_expr(m->expr).op1(), m->op1_bv);
  };

  auto factor_lt = [](const factor_kind &a, const factor_kind &b)
  {
    if(a.index() != b.index())
      return a.index() < b.index();
    if(std::holds_alternative<bvt>(a))
      return std::get<bvt>(a) < std::get<bvt>(b);
    return std::get<std::size_t>(a) < std::get<std::size_t>(b);
  };

  std::vector<std::pair<approximationt *, std::vector<factor_kind>>> mult_flats;
  for(auto &entry : result_bv_index)
  {
    auto *m = entry.second;
    std::vector<factor_kind> factors;
    flatten_mult(m, factors);
    std::sort(factors.begin(), factors.end(), factor_lt);
    mult_flats.emplace_back(m, std::move(factors));
  }

  std::size_t pairs_found = 0;
  for(std::size_t i = 0; i < mult_flats.size(); ++i)
  {
    for(std::size_t j = i + 1; j < mult_flats.size(); ++j)
    {
      if(mult_flats[i].first->expr.type() != mult_flats[j].first->expr.type())
        continue;
      if(mult_flats[i].second == mult_flats[j].second)
      {
        bv_utils.set_equal(
          mult_flats[i].first->result_bv, mult_flats[j].first->result_bv);
        ++pairs_found;
      }
    }
  }

  if(pairs_found > 0)
  {
    log.status() << "BV-Refinement: detected " << pairs_found
                 << " commutative/associative multiplier pair(s)"
                 << messaget::eom;
  }

  // Distributivity: for each mult m_dist whose expression has the form
  // mult(f, plus(p, q)) (or mult(plus(p, q), f)), search for two other
  // mult approximations m_p with expr ~ mult(f, p) and m_q with
  // expr ~ mult(f, q). If both exist, assert
  //   m_dist.result_bv == m_p.result_bv + m_q.result_bv (mod 2^n).
  // Sound because bit-vector multiplication distributes over addition.
  std::size_t dist_found = 0;

  // Helper: does a mult approximation's expression match mult(x, y)
  // (in either operand order)?
  auto mult_matches =
    [](const approximationt &m, const exprt &x, const exprt &y)
  {
    const auto &m0 = to_binary_expr(m.expr).op0();
    const auto &m1 = to_binary_expr(m.expr).op1();
    return (m0 == x && m1 == y) || (m0 == y && m1 == x);
  };

  for(auto &m_dist : approximations)
  {
    if(m_dist.expr.id() != ID_mult || m_dist.expr.operands().size() != 2)
      continue;
    const typet &t = m_dist.expr.type();
    if(t.id() != ID_unsignedbv && t.id() != ID_signedbv)
      continue;

    // Look for plus operand.
    for(std::size_t side = 0; side < 2; ++side)
    {
      const exprt &factor = side == 0 ? to_binary_expr(m_dist.expr).op0()
                                      : to_binary_expr(m_dist.expr).op1();
      const exprt &sum = side == 0 ? to_binary_expr(m_dist.expr).op1()
                                   : to_binary_expr(m_dist.expr).op0();
      if(sum.id() != ID_plus || sum.operands().size() != 2)
        continue;
      const exprt &p = to_binary_expr(sum).op0();
      const exprt &q = to_binary_expr(sum).op1();

      // Find m_p (factor*p) and m_q (factor*q).
      approximationt *m_p = nullptr;
      approximationt *m_q = nullptr;
      for(auto &candidate : approximations)
      {
        if(&candidate == &m_dist)
          continue;
        if(
          candidate.expr.id() != ID_mult ||
          candidate.expr.operands().size() != 2)
          continue;
        if(candidate.expr.type() != t)
          continue;
        if(!m_p && mult_matches(candidate, factor, p))
          m_p = &candidate;
        else if(!m_q && mult_matches(candidate, factor, q))
          m_q = &candidate;
      }

      if(m_p != nullptr && m_q != nullptr)
      {
        // Assert m_dist.result_bv == m_p.result_bv + m_q.result_bv.
        bvt sum_bv = bv_utils.add(m_p->result_bv, m_q->result_bv);
        bv_utils.set_equal(m_dist.result_bv, sum_bv);
        ++dist_found;
        break;
      }
    }
  }

  if(dist_found > 0)
  {
    log.status() << "BV-Refinement: detected " << dist_found
                 << " distributive multiplier triple(s)" << messaget::eom;
  }
}

std::string bv_refinementt::approximationt::as_string() const
{
  return std::to_string(id_nr)+"/"+id2string(expr.id());
}

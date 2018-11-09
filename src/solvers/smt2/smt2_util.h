/*******************************************************************\

Module: SMT2 solver

Author: Romain Brenguier <romain.brenguier@diffblue.com>

*******************************************************************/

/// \file
/// Helper functions for constructing standard SMT2 expressions

#ifndef CPROVER_SOLVERS_SMT2_SMT2_UTIL_H
#define CPROVER_SOLVERS_SMT2_SMT2_UTIL_H

#include "smt2_ast.h"

inline smt2_astt smt2_and(smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{ID_and}},
                                    {std::move(ast1), std::move(ast2)}};
}

inline smt2_astt smt2_bv(const mp_integer &index, const mp_integer &width)
{
  smt2_symbolt bv{"bv" + integer2string(index)};
  return smt2_identifiert{std::move(bv), {smt2_constantt::make(width)}};
}

inline smt2_astt smt2_bvadd(smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvadd"}},
                                    {std::move(ast1), std::move(ast2)}};
}

inline smt2_astt smt2_bvand(smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvand"}},
                                    {std::move(ast1), std::move(ast2)}};
}

inline smt2_astt smt2_bvmul(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvmul"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvlshr(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvlshr"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvnot(smt2_astt arg)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvnot"}},
                                    {std::move(arg)}};
}

inline smt2_astt smt2_bvneg(smt2_astt arg)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvneg"}},
                                    {std::move(arg)}};
}

inline smt2_astt smt2_bvor(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvor"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvsdiv(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvsdiv"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvsge(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvsge"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvshl(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvshl"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvslt(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvslt"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvsrem(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvsrem"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvsub(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvsub"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvudiv(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvudiv"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvuge(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvuge"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_bvurem(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"bvurem"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_concat(smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"concat"}},
                                    {std::move(ast1), std::move(ast2)}};
}

inline smt2_identifiert
smt2_extract(const mp_integer &width, const mp_integer &offset)
{
  return smt2_identifiert{
    smt2_symbolt{"extract"},
    {smt2_constantt::make(width), smt2_constantt::make(offset)}};
}

inline smt2_astt smt2_eq(smt2_astt left, smt2_astt right)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{ID_equal}},
                                    {std::move(left), std::move(right)}};
}

inline smt2_astt
smt2_fp_add(smt2_astt rounding_mode, smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{
    smt2_identifiert{smt2_symbolt{"fp.add"}},
    {std::move(rounding_mode), std::move(ast1), std::move(ast2)}};
}

inline smt2_astt
smt2_fp_div(smt2_astt rounding_mode, smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{
    smt2_identifiert{smt2_symbolt{"fp.sub"}},
    {std::move(rounding_mode), std::move(ast1), std::move(ast2)}};
}

inline smt2_astt smt2_fp_is_infinite(smt2_astt arg)
{
  return smt2_function_applicationt{
    smt2_identifiert{smt2_symbolt{"fp.isInfinite"}}, {std::move(arg)}};
}

inline smt2_astt smt2_fp_is_nan(smt2_astt arg)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"fp.isNaN"}},
                                    {std::move(arg)}};
}

inline smt2_astt smt2_fp_is_normal(smt2_astt arg)
{
  return smt2_function_applicationt{
    smt2_identifiert{smt2_symbolt{"fp.isNormal"}}, {std::move(arg)}};
}

inline smt2_astt smt2_fp_is_zero(smt2_astt arg)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"fp.isZero"}},
                                    {std::move(arg)}};
}

inline smt2_astt
smt2_fp_mul(smt2_astt rounding_mode, smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{
    smt2_identifiert{smt2_symbolt{"fp.mul"}},
    {std::move(rounding_mode), std::move(ast1), std::move(ast2)}};
}

inline smt2_astt
smt2_fp_sub(smt2_astt rounding_mode, smt2_astt ast1, smt2_astt ast2)
{
  return smt2_function_applicationt{
    smt2_identifiert{smt2_symbolt{"fp.sub"}},
    {std::move(rounding_mode), std::move(ast1), std::move(ast2)}};
}

inline smt2_astt smt2_implies(smt2_astt left, smt2_astt right)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{ID_implies}},
                                    {std::move(left), std::move(right)}};
}

inline smt2_astt
smt2_ite(smt2_astt condition, smt2_astt true_case, smt2_astt false_case)
{
  return smt2_function_applicationt{
    smt2_identifiert{smt2_symbolt{"ite"}},
    {std::move(condition), std::move(true_case), std::move(false_case)}};
}

inline smt2_astt smt2_minus(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{ID_minus}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_astt smt2_not(smt2_astt ast)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{ID_not}},
                                    {std::move(ast)}};
}

inline smt2_astt smt2_or(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{ID_or}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_identifiert smt2_repeat(smt2_constantt times)
{
  return smt2_identifiert{smt2_symbolt{"repeat"}, {std::move(times)}};
}

inline smt2_astt smt2_select(smt2_astt arg1, smt2_astt arg2)
{
  return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"select"}},
                                    {std::move(arg1), std::move(arg2)}};
}

inline smt2_identifiert smt2_sign_extend(smt2_constantt constant)
{
  return smt2_identifiert{smt2_symbolt{"sign_extend"}, {std::move(constant)}};
}

inline smt2_identifiert smt2_zero_extend(const mp_integer &width)
{
  return smt2_identifiert{smt2_symbolt{"zero_extend"},
                          {smt2_constantt::make(width)}};
}

#endif // CPROVER_SOLVERS_SMT2_SMT2_UTIL_H

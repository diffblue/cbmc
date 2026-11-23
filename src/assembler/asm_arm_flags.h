/*******************************************************************\

Module: Inline assembly: ARM condition flags

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// The NZCV condition flags and condition codes shared by AArch64 and AArch32

#ifndef CPROVER_ASSEMBLER_ASM_ARM_FLAGS_H
#define CPROVER_ASSEMBLER_ASM_ARM_FLAGS_H

#include "asm_bv_util.h"
#include "asm_semantics.h"

#include <set>

namespace asm_arm // NOLINT
{
inline const std::set<std::string> &condition_codes()
{
  static const std::set<std::string> codes = {
    "eq",
    "ne",
    "cs",
    "hs",
    "cc",
    "lo",
    "mi",
    "pl",
    "vs",
    "vc",
    "hi",
    "ls",
    "ge",
    "lt",
    "gt",
    "le",
    "al"};
  return codes;
}

inline exprt condition(const std::string &cc, asm_lowering_contextt &ctx)
{
  const exprt n = ctx.flag("n"), z = ctx.flag("z"), c = ctx.flag("c"),
              v = ctx.flag("v");

  if(cc == "eq")
    return z;
  if(cc == "ne")
    return not_exprt{z};
  if(cc == "cs" || cc == "hs")
    return c;
  if(cc == "cc" || cc == "lo")
    return not_exprt{c};
  if(cc == "mi")
    return n;
  if(cc == "pl")
    return not_exprt{n};
  if(cc == "vs")
    return v;
  if(cc == "vc")
    return not_exprt{v};
  if(cc == "hi")
    return and_exprt{c, not_exprt{z}};
  if(cc == "ls")
    return or_exprt{not_exprt{c}, z};
  if(cc == "ge")
    return equal_exprt{n, v};
  if(cc == "lt")
    return notequal_exprt{n, v};
  if(cc == "gt")
    return and_exprt{not_exprt{z}, equal_exprt{n, v}};
  if(cc == "le")
    return or_exprt{z, notequal_exprt{n, v}};
  if(cc == "al" || cc == "nv")
    return true_exprt{};
  return nil_exprt{};
}

/// set N and Z from \p result
inline void
set_nz(asm_lowering_contextt &ctx, const exprt &result, std::size_t width)
{
  ctx.assign(ctx.flag("n"), asm_bv::msb(result, width));
  ctx.assign(ctx.flag("z"), asm_bv::is_zero(result));
}

/// flags of \p result = \p a + \p b + \p carry_in
inline void set_add_flags(
  asm_lowering_contextt &ctx,
  const exprt &a,
  const exprt &b,
  const exprt &carry_in,
  const exprt &result,
  std::size_t width)
{
  set_nz(ctx, result, width);
  ctx.assign(ctx.flag("c"), asm_bv::carry_add(a, b, carry_in, width));
  ctx.assign(ctx.flag("v"), asm_bv::overflow_add(a, b, result, width));
}

/// flags of \p result = \p a - \p b, which ARM computes as
/// a + ~b + 1: C is set if there is no borrow
inline void set_sub_flags(
  asm_lowering_contextt &ctx,
  const exprt &a,
  const exprt &b,
  const exprt &result,
  std::size_t width)
{
  set_nz(ctx, result, width);
  ctx.assign(
    ctx.flag("c"),
    not_exprt{asm_bv::borrow_sub(a, b, asm_bv::constant(0, width), width)});
  ctx.assign(ctx.flag("v"), asm_bv::overflow_sub(a, b, result, width));
}

/// flags of a logical operation with result \p result
inline void set_logic_flags(
  asm_lowering_contextt &ctx,
  const exprt &result,
  std::size_t width)
{
  set_nz(ctx, result, width);
  ctx.assign(ctx.flag("c"), false_exprt{});
  ctx.assign(ctx.flag("v"), false_exprt{});
}
} // namespace asm_arm

#endif // CPROVER_ASSEMBLER_ASM_ARM_FLAGS_H

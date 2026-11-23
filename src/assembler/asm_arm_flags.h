/*******************************************************************\

Module: Inline assembly: ARM condition flags

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// The NZCV condition flags, condition codes, and barriers shared by AArch64
/// and AArch32

#ifndef CPROVER_ASSEMBLER_ASM_ARM_FLAGS_H
#define CPROVER_ASSEMBLER_ASM_ARM_FLAGS_H

#include <util/suffix.h>

#include "asm_bv_util.h"
#include "asm_semantics.h"

#include <cctype>
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

/// Lower the barrier \p m (`dmb`, `dsb`, or `isb`) of \p instruction, whose
/// option (if any) selects the accesses that are ordered.
/// \return false if the option is not understood
inline bool lower_barrier(
  const std::string &m,
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx)
{
  std::string option = "sy";
  if(!instruction.operands.empty())
  {
    if(
      instruction.operands.size() != 1 || instruction.operands[0].size() != 1 ||
      !instruction.operands[0][0].is_identifier())
    {
      return ctx.fail("unsupported option of " + m);
    }
    option = instruction.operands[0][0].text;
    for(auto &c : option)
      c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
  }

  if(m == "isb")
  {
    if(option != "sy")
      return ctx.fail("unsupported option of isb");
    // orders nothing by itself, needs to be combined with a branch
    ctx.fence(false, false, false, false, false);
    return true;
  }

  // the option selects the accesses being ordered
  if(option == "sy" || option == "ish" || option == "osh" || option == "nsh")
    ctx.fence(true, true, true, true, true);
  else if(has_suffix(option, "ld")) // loads before loads and stores
    ctx.fence(false, true, true, false, true);
  else if(has_suffix(option, "st")) // stores before stores
    ctx.fence(true, false, false, false, true);
  else
    return ctx.fail("unsupported option of " + m);
  return true;
}
} // namespace asm_arm

#endif // CPROVER_ASSEMBLER_ASM_ARM_FLAGS_H

/*******************************************************************\

Module: Inline assembly: AArch64 instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Instruction semantics for AArch64 (A64 instruction set, GNU syntax)

#include "asm_aarch64.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>

#include "asm_arm_flags.h"
#include "asm_bv_util.h"
#include "asm_semantics.h"

#include <algorithm>
#include <cctype>
#include <map>
#include <set>

using asm_bv::bool_to_bv;
using asm_bv::borrow_sub;
using asm_bv::bv;
using asm_bv::carry_add;
using asm_bv::constant;
using asm_bv::even_parity_low_byte;
using asm_bv::extract;
using asm_bv::is_zero;
using asm_bv::msb;
using asm_bv::overflow_add;
using asm_bv::overflow_sub;
using asm_bv::replace_bits;
using asm_bv::resize;
using asm_bv::sign_extend;

namespace
{
struct a64_operandt
{
  enum class kindt
  {
    REGISTER,
    IMMEDIATE,
    MEMORY,
    /// a condition (eq, ne, ...) or other name, in `name`
    NAME
  };

  kindt kind = kindt::REGISTER;

  // REGISTER: storage (64 bits) and the width of the access
  exprt storage;
  std::size_t width = 64;
  /// xzr/wzr: reads zero, writes are discarded
  bool zero_register = false;

  // IMMEDIATE
  exprt value;

  // MEMORY: the address
  exprt address;
  /// for memory operands bound to a C lvalue: that lvalue and its width
  exprt lvalue;
  std::size_t natural_width = 0;

  // NAME
  std::string name;
};

class asm_aarch64_semanticst : public asm_semanticst
{
public:
  asm_aarch64_semanticst()
  {
    syntax_conventions.line_comments = {"//"};
    syntax_conventions.separators = ";";
  }

  std::string name() const override
  {
    return "AArch64";
  }

  const asm_syntaxt &syntax() const override
  {
    return syntax_conventions;
  }

  std::size_t register_width() const override
  {
    return 64;
  }

  bool reference_widens(const std::string &modifier, std::size_t natural_width)
    const override
  {
    const std::size_t read = modifier == "w" ? 32 : 64;
    return read > natural_width;
  }

  constraint_classt classify_constraint(
    const std::string &constraint,
    std::size_t &pos,
    std::string &) const override
  {
    switch(constraint[pos])
    {
    case 'Q':
      return constraint_classt::MEMORY;
    case 'U':
      // Ump, Utf and the like: memory operands for pair accesses
      if(pos + 2 < constraint.size())
      {
        pos += 2;
        return constraint_classt::MEMORY;
      }
      return constraint_classt::UNKNOWN;
    case 'I':
    case 'J':
    case 'K':
    case 'L':
    case 'M':
    case 'N':
    case 'Z':
      return constraint_classt::IMMEDIATE;
    default:
      // w, x, y: FP/SIMD registers are not modelled
      return constraint_classt::UNKNOWN;
    }
  }

  bool is_flag_output_condition(const std::string &condition) const override
  {
    return asm_arm::condition_codes().count(condition) != 0 &&
           condition != "al";
  }

  exprt
  condition(const std::string &cc, asm_lowering_contextt &ctx) const override
  {
    return asm_arm::condition(cc, ctx);
  }

  bool lower(const asm_instructiont &instruction, asm_lowering_contextt &ctx)
    const override;

protected:
  asm_syntaxt syntax_conventions;

  bool parse_register_name(
    const std::string &name,
    asm_lowering_contextt &ctx,
    a64_operandt &operand) const;

  bool parse_operand(
    const asm_token_listt &tokens,
    asm_lowering_contextt &ctx,
    a64_operandt &operand) const;

  bool parse_immediate_tokens(
    const asm_token_listt &tokens,
    std::size_t pos,
    asm_lowering_contextt &ctx,
    exprt &value) const;

  exprt read(
    asm_lowering_contextt &ctx,
    const a64_operandt &operand,
    std::size_t width) const;

  bool write(
    asm_lowering_contextt &ctx,
    const a64_operandt &operand,
    std::size_t width,
    const exprt &value) const;

  bool lower_memory(
    const std::string &m,
    std::vector<a64_operandt> &ops,
    const asm_instructiont &instruction,
    asm_lowering_contextt &ctx) const;

public:
  std::string canonical_register(const std::string &name) const override;
};

std::string
asm_aarch64_semanticst::canonical_register(const std::string &raw) const
{
  std::string name = raw;
  for(auto &c : name)
    c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));

  if(name == "sp" || name == "wsp")
    return "sp";
  if(name == "lr")
    return "x30";
  if(name == "fp")
    return "x29";
  if(name.size() >= 2 && name.size() <= 3 && (name[0] == 'x' || name[0] == 'w'))
  {
    const std::string digits = name.substr(1);
    if(std::all_of(
         digits.begin(),
         digits.end(),
         [](char c) { return std::isdigit(static_cast<unsigned char>(c)); }))
    {
      const int n = std::stoi(digits);
      if(n <= 30)
        return "x" + std::to_string(n);
    }
  }
  return {};
}

bool asm_aarch64_semanticst::parse_register_name(
  const std::string &raw,
  asm_lowering_contextt &ctx,
  a64_operandt &operand) const
{
  std::string name = raw;
  for(auto &c : name)
    c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));

  operand.kind = a64_operandt::kindt::REGISTER;

  if(name == "xzr" || name == "wzr")
  {
    operand.zero_register = true;
    operand.width = name[0] == 'x' ? 64 : 32;
    return true;
  }

  if(name == "sp" || name == "wsp")
  {
    operand.storage = ctx.hardware_register("sp");
    operand.width = name == "sp" ? 64 : 32;
    return true;
  }

  if(name == "lr")
    name = "x30";
  else if(name == "fp")
    name = "x29";

  if(name.size() >= 2 && (name[0] == 'x' || name[0] == 'w'))
  {
    const std::string digits = name.substr(1);
    if(
      !digits.empty() && digits.size() <= 2 &&
      std::all_of(
        digits.begin(),
        digits.end(),
        [](char c) { return std::isdigit(static_cast<unsigned char>(c)); }))
    {
      const int n = std::stoi(digits);
      if(n <= 30)
      {
        operand.storage = ctx.hardware_register("x" + std::to_string(n));
        operand.width = name[0] == 'x' ? 64 : 32;
        return true;
      }
    }
  }

  return false;
}

bool asm_aarch64_semanticst::parse_immediate_tokens(
  const asm_token_listt &tokens,
  std::size_t pos,
  asm_lowering_contextt &ctx,
  exprt &value) const
{
  bool negative = false;
  if(pos < tokens.size() && tokens[pos].is_punctuation('-'))
  {
    negative = true;
    ++pos;
  }

  if(pos + 1 != tokens.size())
    return ctx.fail("unsupported immediate");

  const asm_tokent &token = tokens[pos];
  if(token.kind == asm_tokent::kindt::NUMBER)
  {
    value =
      from_integer(negative ? -token.number : token.number, integer_typet{});
    return true;
  }

  if(token.kind == asm_tokent::kindt::OPERAND)
  {
    const asm_operandt &bound = ctx.operands.operands.at(token.index);
    if(bound.kind == asm_operandt::kindt::IMMEDIATE)
      value = ctx.operand_immediate(token.index);
    else
      return ctx.fail(
        "operand %" + std::to_string(token.index) + " is not an immediate");
    if(negative)
      value = unary_minus_exprt{value};
    return true;
  }

  return ctx.fail("unsupported immediate");
}

bool asm_aarch64_semanticst::parse_operand(
  const asm_token_listt &tokens,
  asm_lowering_contextt &ctx,
  a64_operandt &operand) const
{
  if(tokens.empty())
    return ctx.fail("empty operand");

  const asm_tokent &first = tokens[0];

  // immediate
  if(first.is_punctuation('#'))
  {
    operand.kind = a64_operandt::kindt::IMMEDIATE;
    return parse_immediate_tokens(tokens, 1, ctx, operand.value);
  }

  if(first.kind == asm_tokent::kindt::NUMBER || first.is_punctuation('-'))
  {
    operand.kind = a64_operandt::kindt::IMMEDIATE;
    return parse_immediate_tokens(tokens, 0, ctx, operand.value);
  }

  // memory: [base] or [base, #offset]
  if(first.is_punctuation('['))
  {
    if(!tokens.back().is_punctuation(']'))
      return ctx.fail("unsupported addressing mode (writeback?)");

    std::vector<asm_token_listt> parts{{}};
    for(std::size_t i = 1; i + 1 < tokens.size(); ++i)
    {
      if(tokens[i].is_punctuation(','))
        parts.emplace_back();
      else
        parts.back().push_back(tokens[i]);
    }

    a64_operandt base;
    if(
      !parse_operand(parts[0], ctx, base) ||
      base.kind != a64_operandt::kindt::REGISTER || base.width != 64)
    {
      return ctx.fail("unsupported base register");
    }

    exprt address = typecast_exprt{
      resize(read(ctx, base, 64), config.ansi_c.pointer_width),
      pointer_type(char_type())};

    if(parts.size() == 2)
    {
      a64_operandt offset;
      if(
        !parse_operand(parts[1], ctx, offset) ||
        offset.kind != a64_operandt::kindt::IMMEDIATE)
      {
        return ctx.fail("unsupported offset");
      }
      address = plus_exprt{
        address,
        typecast_exprt::conditional_cast(
          offset.value, signedbv_typet{config.ansi_c.pointer_width})};
    }
    else if(parts.size() > 2)
      return ctx.fail("unsupported addressing mode");

    operand.kind = a64_operandt::kindt::MEMORY;
    operand.address = address;
    return true;
  }

  if(tokens.size() == 1 && first.kind == asm_tokent::kindt::OPERAND)
  {
    const asm_operandt &bound = ctx.operands.operands.at(first.index);
    switch(bound.kind)
    {
    case asm_operandt::kindt::REGISTER:
      operand.kind = a64_operandt::kindt::REGISTER;
      operand.storage = ctx.operand_storage(first.index);
      if(first.modifier.empty() || first.modifier == "x")
        operand.width = 64;
      else if(first.modifier == "w")
        operand.width = 32;
      else
        return ctx.fail("unsupported operand modifier %" + first.modifier);
      return true;

    case asm_operandt::kindt::MEMORY:
      if(!first.modifier.empty())
        return ctx.fail("unsupported operand modifier %" + first.modifier);
      operand.kind = a64_operandt::kindt::MEMORY;
      operand.address = ctx.operand_address(first.index);
      operand.lvalue = dereference_exprt{ctx.operand_address(first.index)};
      operand.natural_width = ctx.operand_width(first.index);
      return true;

    case asm_operandt::kindt::IMMEDIATE:
      operand.kind = a64_operandt::kindt::IMMEDIATE;
      operand.value = ctx.operand_immediate(first.index);
      return true;

    case asm_operandt::kindt::FLAG_OUTPUT:
      return ctx.fail("flag output used in template");
    }
  }

  if(tokens.size() == 1 && first.is_identifier())
  {
    if(parse_register_name(first.text, ctx, operand))
      return true;
    operand.kind = a64_operandt::kindt::NAME;
    operand.name = first.text;
    for(auto &c : operand.name)
      c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    return true;
  }

  if(
    tokens.size() == 1 && (first.kind == asm_tokent::kindt::LOCAL_LABEL ||
                           first.kind == asm_tokent::kindt::C_LABEL))
  {
    operand.kind = a64_operandt::kindt::NAME;
    return true;
  }

  return ctx.fail("unsupported operand");
}

exprt asm_aarch64_semanticst::read(
  asm_lowering_contextt &ctx,
  const a64_operandt &operand,
  std::size_t width) const
{
  switch(operand.kind)
  {
  case a64_operandt::kindt::REGISTER:
    if(operand.zero_register)
      return constant(0, width);
    if(width == 64)
      return operand.storage;
    return extract(operand.storage, 0, width);

  case a64_operandt::kindt::IMMEDIATE:
    if(operand.value.type().id() == ID_integer)
    {
      return constant(
        numeric_cast_v<mp_integer>(to_constant_expr(operand.value)), width);
    }
    return typecast_exprt::conditional_cast(operand.value, bv(width));

  case a64_operandt::kindt::MEMORY:
    if(ctx.exclusive_open())
    {
      ctx.fail("memory access between load-exclusive and store-exclusive");
      return ctx.nondet(bv(width));
    }
    if(operand.lvalue.is_not_nil() && operand.natural_width == width)
      return ctx.to_bits(operand.lvalue, width);
    return ctx.memory(operand.address, width);

  case a64_operandt::kindt::NAME:
    break;
  }

  ctx.fail("unsupported operand " + operand.name);
  return ctx.nondet(bv(width));
}

bool asm_aarch64_semanticst::write(
  asm_lowering_contextt &ctx,
  const a64_operandt &operand,
  std::size_t width,
  const exprt &value) const
{
  switch(operand.kind)
  {
  case a64_operandt::kindt::REGISTER:
    if(operand.zero_register)
      return true;
    // writes to w registers zero the upper half
    ctx.assign(operand.storage, resize(resize(value, width), 64));
    return true;

  case a64_operandt::kindt::MEMORY:
    if(ctx.exclusive_open())
      return ctx.fail(
        "memory access between load-exclusive and store-exclusive");
    if(operand.lvalue.is_not_nil() && operand.natural_width == width)
    {
      ctx.assign(
        operand.lvalue,
        ctx.from_bits(resize(value, width), operand.lvalue.type()));
    }
    else
      ctx.assign(ctx.memory(operand.address, width), resize(value, width));
    return true;

  case a64_operandt::kindt::IMMEDIATE:
  case a64_operandt::kindt::NAME:
    break;
  }

  return ctx.fail("invalid destination");
}

/// Split \p rest, the part of a mnemonic after its operation, into
/// acquire/release and size parts: e.g. "alb" is "al" and 8 bits.
static bool memory_order_and_size(
  const std::string &rest,
  bool allow_acquire,
  bool &acquire,
  bool &release,
  std::size_t &size)
{
  std::string r = rest;
  size = 0;
  if(!r.empty() && (r.back() == 'b' || r.back() == 'h'))
  {
    size = r.back() == 'b' ? 8 : 16;
    r.pop_back();
  }
  acquire = release = false;
  if(r == "a" && allow_acquire)
    acquire = true;
  else if(r == "l")
    release = true;
  else if(r == "al" && allow_acquire)
    acquire = release = true;
  else if(!r.empty())
    return false;
  return true;
}

bool asm_aarch64_semanticst::lower_memory(
  const std::string &m,
  std::vector<a64_operandt> &ops,
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx) const
{
  auto temp = [&](const exprt &value, const std::string &suffix)
  {
    const symbol_exprt t = ctx.temporary(value.type(), suffix);
    ctx.assign(t, value);
    return t;
  };

  auto memory_operand = [&](std::size_t i)
  { return i < ops.size() && ops[i].kind == a64_operandt::kindt::MEMORY; };

  auto register_operand = [&](std::size_t i)
  { return i < ops.size() && ops[i].kind == a64_operandt::kindt::REGISTER; };

  // plain loads and stores
  {
    static const std::map<std::string, std::pair<std::size_t, bool>> loads = {
      {"ldr", {0, false}},   {"ldrb", {8, false}},   {"ldrh", {16, false}},
      {"ldrsb", {8, true}},  {"ldrsh", {16, true}},  {"ldrsw", {32, true}},
      {"ldur", {0, false}},  {"ldurb", {8, false}},  {"ldurh", {16, false}},
      {"ldar", {0, false}},  {"ldarb", {8, false}},  {"ldarh", {16, false}},
      {"ldapr", {0, false}}, {"ldaprb", {8, false}}, {"ldaprh", {16, false}},
      {"ldxr", {0, false}},  {"ldxrb", {8, false}},  {"ldxrh", {16, false}},
      {"ldaxr", {0, false}}, {"ldaxrb", {8, false}}, {"ldaxrh", {16, false}}};

    auto it = loads.find(m);
    if(it != loads.end())
    {
      if(ops.size() != 2 || !register_operand(0) || !memory_operand(1))
        return ctx.fail("unsupported operands of " + m);
      const std::size_t rw = ops[0].width;
      const std::size_t size = it->second.first == 0 ? rw : it->second.first;
      const bool exclusive = m.find("xr") != std::string::npos;
      const bool acquire = m.compare(0, 3, "lda") == 0;
      const exprt loaded = read(ctx, ops[1], size);
      write(
        ctx,
        ops[0],
        rw,
        it->second.second ? sign_extend(loaded, size, rw) : resize(loaded, rw));
      if(acquire)
        ctx.fence(false, true, true, false, true);
      if(exclusive)
        ctx.begin_exclusive();
      return true;
    }
  }

  {
    static const std::map<std::string, std::size_t> stores = {
      {"str", 0},
      {"strb", 8},
      {"strh", 16},
      {"stur", 0},
      {"sturb", 8},
      {"sturh", 16},
      {"stlr", 0},
      {"stlrb", 8},
      {"stlrh", 16}};
    auto it = stores.find(m);
    if(it != stores.end())
    {
      if(ops.size() != 2 || !register_operand(0) || !memory_operand(1))
        return ctx.fail("unsupported operands of " + m);
      const std::size_t size = it->second == 0 ? ops[0].width : it->second;
      if(m.compare(0, 4, "stlr") == 0)
        ctx.fence(true, false, true, false, true);
      return write(ctx, ops[1], size, read(ctx, ops[0], size));
    }
  }

  // store-exclusive: Ws, Rt, [Xn]
  {
    static const std::map<std::string, std::size_t> stores = {
      {"stxr", 0},
      {"stxrb", 8},
      {"stxrh", 16},
      {"stlxr", 0},
      {"stlxrb", 8},
      {"stlxrh", 16}};
    auto it = stores.find(m);
    if(it != stores.end())
    {
      if(
        ops.size() != 3 || !register_operand(0) || !register_operand(1) ||
        !memory_operand(2))
      {
        return ctx.fail("unsupported operands of " + m);
      }
      const std::size_t size = it->second == 0 ? ops[1].width : it->second;
      if(ctx.exclusive_cleared())
      {
        // the store fails, and does not store
        ctx.clear_exclusive();
        return write(ctx, ops[0], 32, constant(1, 32));
      }
      // The store may fail spuriously; it can succeed without a
      // load-exclusive in this statement if the monitor was set before.
      if(ctx.exclusive_open())
        ctx.end_exclusive();
      if(m.compare(0, 4, "stlx") == 0)
        ctx.fence(true, false, true, false, true);
      const symbol_exprt success = temp(ctx.nondet(bool_typet{}), "success");
      const exprt value = read(ctx, ops[1], size);
      const auto store = ctx.begin_conditional(success);
      if(!write(ctx, ops[2], size, value))
        return false;
      ctx.end_conditional(store);
      ctx.clear_exclusive();
      return write(
        ctx, ops[0], 32, if_exprt{success, constant(0, 32), constant(1, 32)});
    }
  }

  // LSE atomics
  static const std::vector<std::string> lse_operations = {
    "add", "clr", "eor", "set", "smax", "smin", "umax", "umin"};

  for(const std::string prefix : {"ld", "st"})
  {
    if(m.compare(0, 2, prefix) != 0)
      continue;
    for(const auto &op : lse_operations)
    {
      if(m.compare(2, op.size(), op) != 0)
        continue;
      bool acquire, release;
      std::size_t size;
      if(!memory_order_and_size(
           m.substr(2 + op.size()), prefix == "ld", acquire, release, size))
      {
        continue;
      }

      const bool returns = prefix == "ld";
      if(
        ops.size() != (returns ? 3u : 2u) || !register_operand(0) ||
        (returns && !register_operand(1)) || !memory_operand(ops.size() - 1))
      {
        return ctx.fail("unsupported operands of " + m);
      }
      const std::size_t w = size == 0 ? ops[0].width : size;
      ctx.mark_atomic();
      if(release)
        ctx.fence(true, false, true, false, true);
      const symbol_exprt old = temp(read(ctx, ops.back(), w), "old");
      const symbol_exprt arg = temp(read(ctx, ops[0], w), "arg");
      const signedbv_typet s{w};
      const exprt sold = typecast_exprt{old, s}, sarg = typecast_exprt{arg, s};
      exprt result;
      if(op == "add")
        result = plus_exprt{old, arg};
      else if(op == "clr")
        result = bitand_exprt{old, bitnot_exprt{arg}};
      else if(op == "eor")
        result = bitxor_exprt{old, arg};
      else if(op == "set")
        result = bitor_exprt{old, arg};
      else if(op == "smax")
        result = if_exprt{binary_relation_exprt{sold, ID_ge, sarg}, old, arg};
      else if(op == "smin")
        result = if_exprt{binary_relation_exprt{sold, ID_le, sarg}, old, arg};
      else if(op == "umax")
        result = if_exprt{binary_relation_exprt{old, ID_ge, arg}, old, arg};
      else
        result = if_exprt{binary_relation_exprt{old, ID_le, arg}, old, arg};
      if(!write(ctx, ops.back(), w, result))
        return false;
      if(
        returns && !write(ctx, ops[1], ops[1].width, resize(old, ops[1].width)))
        return false;
      if(acquire)
        ctx.fence(false, true, true, false, true);
      return true;
    }
  }

  // swp and cas: Rs, Rt, [Xn]
  for(const std::string op : {"swp", "cas"})
  {
    if(m.compare(0, 3, op) != 0)
      continue;
    bool acquire, release;
    std::size_t size;
    if(!memory_order_and_size(m.substr(3), true, acquire, release, size))
      continue;
    if(
      ops.size() != 3 || !register_operand(0) || !register_operand(1) ||
      !memory_operand(2))
    {
      return ctx.fail("unsupported operands of " + m);
    }
    const std::size_t w = size == 0 ? ops[0].width : size;
    ctx.mark_atomic();
    if(release)
      ctx.fence(true, false, true, false, true);
    const symbol_exprt old = temp(read(ctx, ops[2], w), "old");
    const symbol_exprt rs = temp(read(ctx, ops[0], w), "rs");
    const symbol_exprt rt = temp(read(ctx, ops[1], w), "rt");
    if(op == "swp")
    {
      // swp Rs, Rt, [Xn]: store Rs, load the old value into Rt
      if(
        !write(ctx, ops[2], w, rs) ||
        !write(ctx, ops[1], ops[1].width, resize(old, ops[1].width)))
      {
        return false;
      }
    }
    else
    {
      // cas Rs, Rt, [Xn]: if the memory equals Rs, store Rt; Rs := old value
      if(
        !write(ctx, ops[2], w, if_exprt{equal_exprt{old, rs}, rt, old}) ||
        !write(ctx, ops[0], ops[0].width, resize(old, ops[0].width)))
      {
        return false;
      }
    }
    if(acquire)
      ctx.fence(false, true, true, false, true);
    return true;
  }

  return ctx.fail("unsupported instruction " + instruction.mnemonic);
}

bool asm_aarch64_semanticst::lower(
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx) const
{
  const std::string &m = instruction.mnemonic;

  if(!instruction.prefixes.empty())
    return ctx.fail("unexpected prefix");

  // hints and environment instructions without effect on the C program
  // state
  if(
    m == "nop" || m == "yield" || m == "wfe" || m == "wfi" || m == "sev" ||
    m == "sevl" || m == "prfm" || m == "hint" || m == "csdb" || m == "esb" ||
    m == "sb")
  {
    return true;
  }

  if(m == "clrex")
  {
    ctx.clear_exclusive();
    return true;
  }

  if(m == "dmb" || m == "dsb" || m == "isb")
    return asm_arm::lower_barrier(m, instruction, ctx);

  // branches: the target is the last operand
  if(
    m == "b" || (m.size() > 2 && m.compare(0, 2, "b.") == 0) || m == "cbz" ||
    m == "cbnz" || m == "tbz" || m == "tbnz")
  {
    if(instruction.operands.empty() || instruction.operands.back().size() != 1)
      return ctx.fail("unsupported branch target");
    const asm_tokent &target = instruction.operands.back().back();

    if(m == "b")
      return ctx.branch(target, true_exprt{});

    if(m[1] == '.')
    {
      const exprt cond = asm_arm::condition(m.substr(2), ctx);
      if(cond.is_nil())
        return ctx.fail("unsupported condition " + m);
      return ctx.branch(target, cond);
    }

    asm_token_listt reg_tokens = instruction.operands[0];
    a64_operandt reg;
    if(
      !parse_operand(reg_tokens, ctx, reg) ||
      reg.kind != a64_operandt::kindt::REGISTER)
    {
      return ctx.fail("unsupported register in " + m);
    }

    if(m == "cbz" || m == "cbnz")
    {
      if(instruction.operands.size() != 2)
        return ctx.fail("unsupported " + m);
      const exprt zero = is_zero(read(ctx, reg, reg.width));
      return ctx.branch(target, m == "cbz" ? zero : exprt{not_exprt{zero}});
    }

    // tbz/tbnz Rt, #bit, label
    if(instruction.operands.size() != 3)
      return ctx.fail("unsupported " + m);
    a64_operandt bit;
    if(
      !parse_operand(instruction.operands[1], ctx, bit) ||
      bit.kind != a64_operandt::kindt::IMMEDIATE)
    {
      return ctx.fail("unsupported bit in " + m);
    }
    const exprt set =
      extractbit_exprt{lshr_exprt{read(ctx, reg, 64), read(ctx, bit, 64)}, 0};
    return ctx.branch(target, m == "tbnz" ? set : exprt{not_exprt{set}});
  }

  std::vector<a64_operandt> ops;
  for(const auto &tokens : instruction.operands)
  {
    a64_operandt op;
    if(
      tokens.size() > 1 && tokens[0].is_identifier() &&
      (tokens[0].text == "lsl" || tokens[0].text == "lsr" ||
       tokens[0].text == "asr" || tokens[0].text == "ror"))
    {
      // a shift, interpreted by the instruction from the tokens
      op.kind = a64_operandt::kindt::NAME;
      op.name = tokens[0].text;
      ops.push_back(op);
      continue;
    }
    if(!parse_operand(tokens, ctx, op))
      return false;
    ops.push_back(op);
  }

  auto is_reg = [&](std::size_t i)
  { return i < ops.size() && ops[i].kind == a64_operandt::kindt::REGISTER; };

  auto temp = [&](const exprt &value, const std::string &suffix)
  {
    const symbol_exprt t = ctx.temporary(value.type(), suffix);
    ctx.assign(t, value);
    return t;
  };

  if(m == "mrs")
  {
    if(
      ops.size() != 2 || !is_reg(0) || ops[1].kind != a64_operandt::kindt::NAME)
      return ctx.fail("unsupported mrs");
    if(ops[1].name == "nzcv")
    {
      // N, Z, C, V are bits 31 to 28
      exprt value = constant(0, 64);
      std::size_t bit = 31;
      for(const char *f : {"n", "z", "c", "v"})
      {
        value = bitor_exprt{
          value,
          shl_exprt{typecast_exprt{ctx.flag(f), bv(64)}, constant(bit--, 64)}};
      }
      return write(ctx, ops[0], 64, value);
    }
    // other system registers: their values are not modeled
    return write(ctx, ops[0], 64, ctx.nondet(bv(64)));
  }

  if(m == "msr")
  {
    if(ops.size() != 2 || ops[0].kind != a64_operandt::kindt::NAME)
      return ctx.fail("unsupported msr");
    const std::string &target = ops[0].name;
    if(target == "nzcv" && is_reg(1))
    {
      const symbol_exprt value = temp(read(ctx, ops[1], 64), "nzcv");
      std::size_t bit = 31;
      for(const char *f : {"n", "z", "c", "v"})
        ctx.assign(ctx.flag(f), extractbit_exprt{value, bit--});
      return true;
    }
    // the interrupt masks have no effect on the C program state
    if(target == "daifset" || target == "daifclr" || target == "daif")
      return true;
    // others (such as fpcr, which sets the rounding mode) are not modeled
    return ctx.fail("unsupported system register " + target);
  }

  if(m == "mov" || m == "mvn")
  {
    if(ops.size() != 2 || !is_reg(0))
      return ctx.fail("unsupported " + m);
    const std::size_t w = ops[0].width;
    const exprt v = read(ctx, ops[1], w);
    return write(ctx, ops[0], w, m == "mvn" ? exprt{bitnot_exprt{v}} : v);
  }

  if(m == "movz" || m == "movk" || m == "movn")
  {
    std::size_t shift = 0;
    if(ops.size() == 3)
    {
      // the shift arrives as a NAME "lsl" followed by an immediate, which
      // the tokenizer keeps in one operand
      const auto &tokens = instruction.operands[2];
      if(
        tokens.size() != 3 || !tokens[0].is_identifier() ||
        tokens[0].text != "lsl" || !tokens[1].is_punctuation('#') ||
        tokens[2].kind != asm_tokent::kindt::NUMBER)
      {
        return ctx.fail("unsupported shift in " + m);
      }
      shift = numeric_cast_v<std::size_t>(tokens[2].number);
    }
    else if(ops.size() != 2)
      return ctx.fail("unsupported " + m);
    if(!is_reg(0))
      return ctx.fail("unsupported " + m);
    const std::size_t w = ops[0].width;
    const exprt imm = shl_exprt{resize(read(ctx, ops[1], 16), w), shift};
    if(m == "movz")
      return write(ctx, ops[0], w, imm);
    if(m == "movn")
      return write(ctx, ops[0], w, bitnot_exprt{imm});
    return write(
      ctx,
      ops[0],
      w,
      replace_bits(read(ctx, ops[0], w), w, shift, 16, read(ctx, ops[1], 16)));
  }

  if(m == "neg" || m == "negs")
  {
    if(ops.size() != 2 || !is_reg(0))
      return ctx.fail("unsupported " + m);
    const std::size_t w = ops[0].width;
    const symbol_exprt src = temp(read(ctx, ops[1], w), "src");
    const symbol_exprt result = temp(unary_minus_exprt{src}, "result");
    if(m == "negs")
      asm_arm::set_sub_flags(ctx, constant(0, w), src, result, w);
    return write(ctx, ops[0], w, result);
  }

  // three-operand data processing: Rd, Rn, Rm|#imm
  static const std::set<std::string> arithmetic = {
    "add",
    "adds",
    "sub",
    "subs",
    "and",
    "ands",
    "orr",
    "eor",
    "bic",
    "bics",
    "orn",
    "eon",
    "lsl",
    "lsr",
    "asr",
    "ror"};

  if(arithmetic.count(m))
  {
    if(ops.size() == 4)
    {
      // an immediate shift of the last operand: add x0, x1, x2, lsl #3
      const auto &tokens = instruction.operands[3];
      if(
        tokens.size() == 3 && tokens[0].is_identifier() &&
        tokens[1].is_punctuation('#') &&
        tokens[2].kind == asm_tokent::kindt::NUMBER &&
        (tokens[0].text == "lsl" || tokens[0].text == "lsr" ||
         tokens[0].text == "asr"))
      {
        const std::size_t w = ops[0].width;
        const exprt v = read(ctx, ops[2], w);
        const std::size_t n = numeric_cast_v<std::size_t>(tokens[2].number);
        a64_operandt shifted;
        shifted.kind = a64_operandt::kindt::IMMEDIATE;
        shifted.value =
          tokens[0].text == "lsl" ? exprt{shl_exprt{v, n}}
          : tokens[0].text == "lsr"
            ? exprt{lshr_exprt{v, n}}
            : exprt{typecast_exprt{
                ashr_exprt{typecast_exprt{v, signedbv_typet{w}}, n}, bv(w)}};
        ops[2] = shifted;
        ops.pop_back();
      }
      else
        return ctx.fail("unsupported operand shift");
    }

    if(ops.size() != 3 || !is_reg(0) || !is_reg(1))
      return ctx.fail("unsupported operands of " + m);

    const std::size_t w = ops[0].width;
    const symbol_exprt a = temp(read(ctx, ops[1], w), "a");
    const symbol_exprt b = temp(read(ctx, ops[2], w), "b");
    exprt result;
    if(m == "add" || m == "adds")
      result = plus_exprt{a, b};
    else if(m == "sub" || m == "subs")
      result = minus_exprt{a, b};
    else if(m == "and" || m == "ands")
      result = bitand_exprt{a, b};
    else if(m == "orr")
      result = bitor_exprt{a, b};
    else if(m == "eor")
      result = bitxor_exprt{a, b};
    else if(m == "bic" || m == "bics")
      result = bitand_exprt{a, bitnot_exprt{b}};
    else if(m == "orn")
      result = bitor_exprt{a, bitnot_exprt{b}};
    else if(m == "eon")
      result = bitxor_exprt{a, bitnot_exprt{b}};
    else
    {
      const exprt n = bitand_exprt{b, constant(w - 1, w)};
      if(m == "lsl")
        result = shl_exprt{a, n};
      else if(m == "lsr")
        result = lshr_exprt{a, n};
      else if(m == "asr")
        result = typecast_exprt{
          ashr_exprt{typecast_exprt{a, signedbv_typet{w}}, n}, bv(w)};
      else
        result = if_exprt{
          is_zero(n),
          a,
          bitor_exprt{
            lshr_exprt{a, n}, shl_exprt{a, minus_exprt{constant(w, w), n}}}};
    }

    const symbol_exprt r = temp(result, "result");
    if(m == "adds")
      asm_arm::set_add_flags(ctx, a, b, constant(0, w), r, w);
    else if(m == "subs")
      asm_arm::set_sub_flags(ctx, a, b, r, w);
    else if(m == "ands" || m == "bics")
      asm_arm::set_logic_flags(ctx, r, w);
    return write(ctx, ops[0], w, r);
  }

  if(m == "cmp" || m == "cmn" || m == "tst")
  {
    if(ops.size() != 2 || !is_reg(0))
      return ctx.fail("unsupported " + m);
    const std::size_t w = ops[0].width;
    const symbol_exprt a = temp(read(ctx, ops[0], w), "a");
    const symbol_exprt b = temp(read(ctx, ops[1], w), "b");
    if(m == "cmp")
      asm_arm::set_sub_flags(ctx, a, b, temp(minus_exprt{a, b}, "r"), w);
    else if(m == "cmn")
    {
      asm_arm::set_add_flags(
        ctx, a, b, constant(0, w), temp(plus_exprt{a, b}, "r"), w);
    }
    else
      asm_arm::set_logic_flags(ctx, temp(bitand_exprt{a, b}, "r"), w);
    return true;
  }

  if(m == "cset" || m == "csetm")
  {
    if(
      ops.size() != 2 || !is_reg(0) || ops[1].kind != a64_operandt::kindt::NAME)
    {
      return ctx.fail("unsupported " + m);
    }
    const exprt cond = asm_arm::condition(ops[1].name, ctx);
    if(cond.is_nil())
      return ctx.fail("unsupported condition " + ops[1].name);
    const std::size_t w = ops[0].width;
    return write(
      ctx,
      ops[0],
      w,
      if_exprt{cond, constant(m == "cset" ? 1 : -1, w), constant(0, w)});
  }

  if(m == "csel" || m == "csinc" || m == "csinv" || m == "csneg")
  {
    if(
      ops.size() != 4 || !is_reg(0) || ops[3].kind != a64_operandt::kindt::NAME)
    {
      return ctx.fail("unsupported " + m);
    }
    const exprt cond = asm_arm::condition(ops[3].name, ctx);
    if(cond.is_nil())
      return ctx.fail("unsupported condition " + ops[3].name);
    const std::size_t w = ops[0].width;
    const exprt a = read(ctx, ops[1], w), b = read(ctx, ops[2], w);
    const exprt alternative = m == "csel" ? b
                              : m == "csinc"
                                ? exprt{plus_exprt{b, constant(1, w)}}
                              : m == "csinv" ? exprt{bitnot_exprt{b}}
                                             : exprt{unary_minus_exprt{b}};
    return write(ctx, ops[0], w, if_exprt{cond, a, alternative});
  }

  return lower_memory(m, ops, instruction, ctx);
}
} // namespace

std::unique_ptr<asm_semanticst> make_asm_aarch64_semantics()
{
  return std::make_unique<asm_aarch64_semanticst>();
}

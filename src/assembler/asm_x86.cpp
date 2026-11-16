/*******************************************************************\

Module: Inline assembly: x86 instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Instruction semantics for x86 (i386 and x86-64), AT&T syntax

#include "asm_x86.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>

#include "asm_bv_util.h"
#include "asm_semantics.h"

#include <algorithm>
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
struct x86_operandt
{
  enum class kindt
  {
    REGISTER,
    IMMEDIATE,
    MEMORY
  };

  kindt kind = kindt::REGISTER;

  // REGISTER
  exprt storage;
  std::size_t offset = 0;
  /// width given by the register name or operand modifier; 0 if unknown
  std::size_t width = 0;
  /// true for the 8-bit registers %ah..%dh and the h modifier
  bool high_byte = false;

  // IMMEDIATE
  exprt value;

  // MEMORY
  exprt address;
  /// segment-relative: an address space the C program does not see
  bool environment = false;
  /// for memory operands bound to a C lvalue: that lvalue, typed
  exprt lvalue;
  /// width of the C lvalue, 0 if unknown
  std::size_t natural_width = 0;
};

const std::set<std::string> &sized_mnemonics()
{
  static const std::set<std::string> mnemonics = {
    "mov", "movabs", "add",   "adc",    "sub",   "sbb",  "and",  "or",
    "xor", "not",    "neg",   "inc",    "dec",   "shl",  "sal",  "shr",
    "sar", "rol",    "ror",   "bt",     "bts",   "btr",  "btc",  "bsf",
    "bsr", "tzcnt",  "lzcnt", "popcnt", "bswap", "xchg", "xadd", "cmpxchg",
    "cmp", "test",   "lea",   "in",     "out"};
  return mnemonics;
}

const std::set<std::string> &condition_codes()
{
  static const std::set<std::string> codes = {
    "o",  "no", "b",  "c",   "nae", "ae",  "nb", "nc", "e", "z",
    "ne", "nz", "be", "na",  "a",   "nbe", "s",  "ns", "p", "pe",
    "np", "po", "l",  "nge", "ge",  "nl",  "le", "ng", "g", "nle"};
  return codes;
}

std::size_t suffix_width(char c)
{
  switch(c)
  {
  case 'b':
    return 8;
  case 'w':
    return 16;
  case 'l':
    return 32;
  case 'q':
    return 64;
  default:
    return 0;
  }
}

class asm_x86_semanticst : public asm_semanticst
{
public:
  explicit asm_x86_semanticst(bool _x86_64) : x86_64(_x86_64)
  {
    syntax_conventions.line_comments = {"#"};
    syntax_conventions.separators = ";";
    syntax_conventions.prefixes = {
      "lock", "rep", "repe", "repz", "repne", "repnz"};

    const char *const legacy[] = {"a", "b", "c", "d"};
    for(const char *r : legacy)
    {
      const std::string canonical = std::string("r") + r + "x";
      if(x86_64)
        registers[canonical] = {canonical, 64, 0};
      registers[std::string("e") + r + "x"] = {canonical, 32, 0};
      registers[std::string(r) + "x"] = {canonical, 16, 0};
      registers[std::string(r) + "l"] = {canonical, 8, 0};
      registers[std::string(r) + "h"] = {canonical, 8, 8};
    }

    const char *const index[] = {"si", "di", "bp", "sp"};
    for(const char *r : index)
    {
      const std::string canonical = std::string("r") + r;
      if(x86_64)
      {
        registers[canonical] = {canonical, 64, 0};
        registers[std::string(r) + "l"] = {canonical, 8, 0};
      }
      registers[std::string("e") + r] = {canonical, 32, 0};
      registers[r] = {canonical, 16, 0};
    }

    if(x86_64)
    {
      for(int i = 8; i <= 15; ++i)
      {
        const std::string canonical = "r" + std::to_string(i);
        registers[canonical] = {canonical, 64, 0};
        registers[canonical + "d"] = {canonical, 32, 0};
        registers[canonical + "w"] = {canonical, 16, 0};
        registers[canonical + "b"] = {canonical, 8, 0};
      }
    }
  }

  std::string name() const override
  {
    return x86_64 ? "x86-64" : "i386";
  }

  const asm_syntaxt &syntax() const override
  {
    return syntax_conventions;
  }

  std::size_t register_width() const override
  {
    return x86_64 ? 64 : 32;
  }

  std::string canonical_register(const std::string &name) const override
  {
    const std::string bare =
      !name.empty() && name[0] == '%' ? name.substr(1) : name;
    const auto it = registers.find(bare);
    return it == registers.end() ? std::string{} : it->second.canonical;
  }

  bool reference_widens(const std::string &modifier, std::size_t natural_width)
    const override
  {
    std::size_t read = natural_width <= 8    ? 8
                       : natural_width <= 16 ? 16
                       : natural_width <= 32 ? 32
                                             : 64;
    if(modifier == "b" || modifier == "h")
      read = 8;
    else if(modifier == "w")
      read = 16;
    else if(modifier == "k")
      read = 32;
    else if(modifier == "q")
      read = 64;
    return read > natural_width;
  }

  constraint_classt classify_constraint(
    const std::string &constraint,
    std::size_t &pos,
    std::string &fixed_register) const override
  {
    switch(constraint[pos])
    {
    case 'a':
      fixed_register = "rax";
      return constraint_classt::FIXED_REGISTER;
    case 'b':
      fixed_register = "rbx";
      return constraint_classt::FIXED_REGISTER;
    case 'c':
      fixed_register = "rcx";
      return constraint_classt::FIXED_REGISTER;
    case 'd':
      fixed_register = "rdx";
      return constraint_classt::FIXED_REGISTER;
    case 'S':
      fixed_register = "rsi";
      return constraint_classt::FIXED_REGISTER;
    case 'D':
      fixed_register = "rdi";
      return constraint_classt::FIXED_REGISTER;
    case 'q':
    case 'Q':
    case 'R':
    case 'l':
    case 'U':
      return constraint_classt::REGISTER;
    case 'I':
    case 'J':
    case 'K':
    case 'L':
    case 'M':
    case 'N':
    case 'O':
    case 'e':
    case 'Z':
    case 'G':
    case 'C':
      return constraint_classt::IMMEDIATE;
    default:
      // A (edx:eax), x87, vector and mask registers are not modelled
      return constraint_classt::UNKNOWN;
    }
  }

  bool is_flag_output_condition(const std::string &condition) const override
  {
    return condition_codes().count(condition) != 0;
  }

  exprt
  condition(const std::string &cc, asm_lowering_contextt &ctx) const override
  {
    const exprt cf = ctx.flag("cf"), zf = ctx.flag("zf"), sf = ctx.flag("sf"),
                of = ctx.flag("of"), pf = ctx.flag("pf");

    if(cc == "o")
      return of;
    if(cc == "no")
      return not_exprt{of};
    if(cc == "b" || cc == "c" || cc == "nae")
      return cf;
    if(cc == "ae" || cc == "nb" || cc == "nc")
      return not_exprt{cf};
    if(cc == "e" || cc == "z")
      return zf;
    if(cc == "ne" || cc == "nz")
      return not_exprt{zf};
    if(cc == "be" || cc == "na")
      return or_exprt{cf, zf};
    if(cc == "a" || cc == "nbe")
      return and_exprt{not_exprt{cf}, not_exprt{zf}};
    if(cc == "s")
      return sf;
    if(cc == "ns")
      return not_exprt{sf};
    if(cc == "p" || cc == "pe")
      return pf;
    if(cc == "np" || cc == "po")
      return not_exprt{pf};
    if(cc == "l" || cc == "nge")
      return notequal_exprt{sf, of};
    if(cc == "ge" || cc == "nl")
      return equal_exprt{sf, of};
    if(cc == "le" || cc == "ng")
      return or_exprt{zf, notequal_exprt{sf, of}};
    if(cc == "g" || cc == "nle")
      return and_exprt{not_exprt{zf}, equal_exprt{sf, of}};
    return nil_exprt{};
  }

  bool lower(const asm_instructiont &instruction, asm_lowering_contextt &ctx)
    const override;

protected:
  bool x86_64;
  asm_syntaxt syntax_conventions;

  struct registert
  {
    std::string canonical;
    std::size_t width;
    std::size_t offset;
  };
  std::map<std::string, registert> registers;

  bool parse_operand(
    const asm_token_listt &tokens,
    asm_lowering_contextt &ctx,
    x86_operandt &operand) const;

  bool parse_register(
    const asm_token_listt &tokens,
    std::size_t &pos,
    asm_lowering_contextt &ctx,
    x86_operandt &operand) const;

  bool parse_immediate(
    const asm_token_listt &tokens,
    std::size_t pos,
    asm_lowering_contextt &ctx,
    exprt &value) const;

  bool parse_memory(
    const asm_token_listt &tokens,
    std::size_t pos,
    bool environment,
    asm_lowering_contextt &ctx,
    x86_operandt &operand) const;

  exprt read(
    asm_lowering_contextt &ctx,
    const x86_operandt &operand,
    std::size_t width) const;

  bool write(
    asm_lowering_contextt &ctx,
    const x86_operandt &operand,
    std::size_t width,
    const exprt &value) const;

  /// the value of a register operand as an address
  exprt
  register_address(asm_lowering_contextt &ctx, const x86_operandt &reg) const;

  void set_result_flags(
    asm_lowering_contextt &ctx,
    const exprt &result,
    std::size_t width) const
  {
    ctx.assign(ctx.flag("zf"), is_zero(result));
    ctx.assign(ctx.flag("sf"), msb(result, width));
    ctx.assign(ctx.flag("pf"), even_parity_low_byte(result));
  }

  void set_logic_flags(
    asm_lowering_contextt &ctx,
    const exprt &result,
    std::size_t width) const
  {
    ctx.assign(ctx.flag("cf"), false_exprt{});
    ctx.assign(ctx.flag("of"), false_exprt{});
    set_result_flags(ctx, result, width);
  }

  void undefined_flags(
    asm_lowering_contextt &ctx,
    std::initializer_list<const char *> names) const
  {
    for(const char *name : names)
      ctx.assign(ctx.flag(name), ctx.nondet(bool_typet{}));
  }

  /// accumulator register (al/ax/eax/rax) of \p width bits
  x86_operandt accumulator(asm_lowering_contextt &ctx, std::size_t width) const
  {
    return named_register(ctx, "rax", width);
  }

  x86_operandt named_register(
    asm_lowering_contextt &ctx,
    const std::string &canonical,
    std::size_t width) const
  {
    x86_operandt op;
    op.kind = x86_operandt::kindt::REGISTER;
    op.storage = ctx.hardware_register(canonical);
    op.width = width;
    return op;
  }

  static std::size_t
  operation_width(const std::vector<x86_operandt> &operands, std::size_t suffix)
  {
    if(suffix != 0)
      return suffix;
    for(const auto &op : operands)
    {
      if(op.kind == x86_operandt::kindt::REGISTER && op.width != 0)
        return op.width;
    }
    for(const auto &op : operands)
    {
      if(op.kind == x86_operandt::kindt::MEMORY && op.natural_width != 0)
        return op.natural_width;
    }
    return 0;
  }

  bool lower_sized(
    const std::string &base,
    std::size_t width,
    std::vector<x86_operandt> &operands,
    const asm_instructiont &instruction,
    asm_lowering_contextt &ctx) const;
};

bool asm_x86_semanticst::parse_register(
  const asm_token_listt &tokens,
  std::size_t &pos,
  asm_lowering_contextt &ctx,
  x86_operandt &operand) const
{
  if(
    pos + 1 < tokens.size() && tokens[pos].is_punctuation('%') &&
    tokens[pos + 1].is_identifier())
  {
    auto it = registers.find(tokens[pos + 1].text);
    if(it == registers.end())
      return ctx.fail("unsupported register %" + tokens[pos + 1].text);
    operand.kind = x86_operandt::kindt::REGISTER;
    operand.storage = ctx.hardware_register(it->second.canonical);
    operand.width = it->second.width;
    operand.offset = it->second.offset;
    pos += 2;
    return true;
  }

  if(pos < tokens.size() && tokens[pos].kind == asm_tokent::kindt::OPERAND)
  {
    const asm_tokent &token = tokens[pos];
    const asm_operandt &bound = ctx.operands.operands.at(token.index);
    if(bound.kind != asm_operandt::kindt::REGISTER)
      return ctx.fail(
        "operand %" + std::to_string(token.index) + " is not a register");

    operand.kind = x86_operandt::kindt::REGISTER;
    operand.storage = ctx.operand_storage(token.index);
    const std::string &m = token.modifier;
    if(m.empty())
    {
      const std::size_t w = ctx.operand_width(token.index);
      operand.width = w <= 8 ? 8 : w <= 16 ? 16 : w <= 32 ? 32 : 64;
      if(operand.width > register_width())
        return ctx.fail("operand too wide");
    }
    else if(m == "b")
      operand.width = 8;
    else if(m == "h")
    {
      operand.width = 8;
      operand.offset = 8;
    }
    else if(m == "w")
      operand.width = 16;
    else if(m == "k")
      operand.width = 32;
    else if(m == "q" && x86_64)
      operand.width = 64;
    else
      return ctx.fail("unsupported operand modifier %" + m);
    ++pos;
    return true;
  }

  return false;
}

bool asm_x86_semanticst::parse_immediate(
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
    if(bound.kind != asm_operandt::kindt::IMMEDIATE)
      return ctx.fail(
        "operand %" + std::to_string(token.index) + " is not an immediate");
    value = ctx.operand_immediate(token.index);
    if(negative)
      value = unary_minus_exprt{value};
    return true;
  }

  return ctx.fail("unsupported immediate");
}

bool asm_x86_semanticst::parse_memory(
  const asm_token_listt &tokens,
  std::size_t pos,
  bool environment,
  asm_lowering_contextt &ctx,
  x86_operandt &operand) const
{
  operand.kind = x86_operandt::kindt::MEMORY;
  operand.environment = environment;

  // a memory operand bound to a C lvalue
  if(
    pos + 1 == tokens.size() &&
    tokens[pos].kind == asm_tokent::kindt::OPERAND &&
    ctx.operands.operands.at(tokens[pos].index).kind ==
      asm_operandt::kindt::MEMORY)
  {
    const std::size_t index = tokens[pos].index;
    if(!tokens[pos].modifier.empty())
      return ctx.fail("unsupported memory operand modifier");
    operand.address = ctx.operand_address(index);
    operand.lvalue = dereference_exprt{ctx.operand_address(index)};
    operand.natural_width = ctx.operand_width(index);
    return true;
  }

  // displacement
  mp_integer displacement = 0;
  exprt displacement_expr = nil_exprt{};
  bool negative = false;
  if(pos < tokens.size() && tokens[pos].is_punctuation('-'))
  {
    negative = true;
    ++pos;
  }
  if(pos < tokens.size() && tokens[pos].kind == asm_tokent::kindt::NUMBER)
  {
    displacement = negative ? -tokens[pos].number : tokens[pos].number;
    ++pos;
  }
  else if(
    pos < tokens.size() && tokens[pos].kind == asm_tokent::kindt::OPERAND &&
    (tokens[pos].modifier == "c" || tokens[pos].modifier == "P" ||
     tokens[pos].modifier.empty()) &&
    ctx.operands.operands.at(tokens[pos].index).kind ==
      asm_operandt::kindt::IMMEDIATE)
  {
    displacement_expr = ctx.operand_immediate(tokens[pos].index);
    if(negative)
      displacement_expr = unary_minus_exprt{displacement_expr};
    ++pos;
  }
  else if(negative)
    return ctx.fail("unsupported displacement");

  const signedbv_typet offset_type{config.ansi_c.pointer_width};
  exprt offset = from_integer(displacement, offset_type);
  if(displacement_expr.is_not_nil())
  {
    offset = plus_exprt{
      offset, typecast_exprt::conditional_cast(displacement_expr, offset_type)};
  }

  if(pos == tokens.size())
  {
    // an absolute address; only meaningful relative to a segment
    if(!environment)
      return ctx.fail("absolute memory operand");
    operand.address = offset;
    return true;
  }

  if(!tokens[pos].is_punctuation('(') || !tokens.back().is_punctuation(')'))
    return ctx.fail("unsupported memory operand");
  ++pos;

  exprt address = nil_exprt{};

  // base
  if(!tokens[pos].is_punctuation(','))
  {
    x86_operandt base;
    if(!parse_register(tokens, pos, ctx, base))
      return ctx.fail("unsupported base register");
    address = register_address(ctx, base);
  }

  // index and scale
  if(tokens[pos].is_punctuation(','))
  {
    ++pos;
    x86_operandt index;
    if(!parse_register(tokens, pos, ctx, index))
      return ctx.fail("unsupported index register");
    mp_integer scale = 1;
    if(tokens[pos].is_punctuation(','))
    {
      ++pos;
      if(tokens[pos].kind != asm_tokent::kindt::NUMBER)
        return ctx.fail("unsupported scale");
      scale = tokens[pos].number;
      ++pos;
    }
    offset = plus_exprt{
      offset,
      mult_exprt{
        typecast_exprt{read(ctx, index, index.width), offset_type},
        from_integer(scale, offset_type)}};
  }

  if(!tokens[pos].is_punctuation(')') || pos + 1 != tokens.size())
    return ctx.fail("unsupported memory operand");

  if(address.is_nil())
  {
    // the address is the index and displacement only; within a segment,
    // the offset is meaningful as such
    operand.address =
      environment ? offset
                  : exprt{typecast_exprt{offset, pointer_type(char_type())}};
  }
  else
    operand.address = plus_exprt{address, offset};

  return true;
}

exprt asm_x86_semanticst::register_address(
  asm_lowering_contextt &ctx,
  const x86_operandt &reg) const
{
  const exprt value = read(ctx, reg, reg.width);
  return typecast_exprt{
    resize(value, config.ansi_c.pointer_width), pointer_type(char_type())};
}

bool asm_x86_semanticst::parse_operand(
  const asm_token_listt &tokens,
  asm_lowering_contextt &ctx,
  x86_operandt &operand) const
{
  if(tokens.empty())
    return ctx.fail("empty operand");

  // immediate
  if(tokens[0].is_punctuation('$'))
  {
    operand.kind = x86_operandt::kindt::IMMEDIATE;
    return parse_immediate(tokens, 1, ctx, operand.value);
  }

  // an operand bound to an immediate is printed with its $
  if(
    tokens.size() == 1 && tokens[0].kind == asm_tokent::kindt::OPERAND &&
    tokens[0].modifier.empty() &&
    ctx.operands.operands.at(tokens[0].index).kind ==
      asm_operandt::kindt::IMMEDIATE)
  {
    operand.kind = x86_operandt::kindt::IMMEDIATE;
    operand.value = ctx.operand_immediate(tokens[0].index);
    return true;
  }

  // segment prefix
  if(
    tokens.size() >= 3 && tokens[0].is_punctuation('%') &&
    tokens[1].is_identifier() && tokens[2].is_punctuation(':'))
  {
    const std::string &segment = tokens[1].text;
    if(segment != "gs" && segment != "fs")
      return ctx.fail("unsupported segment %" + segment);
    return parse_memory(tokens, 3, true, ctx, operand);
  }

  // register
  if(
    tokens.size() <= 2 && (tokens[0].is_punctuation('%') ||
                           (tokens[0].kind == asm_tokent::kindt::OPERAND &&
                            ctx.operands.operands.at(tokens[0].index).kind ==
                              asm_operandt::kindt::REGISTER)))
  {
    std::size_t pos = 0;
    if(!parse_register(tokens, pos, ctx, operand))
      return false;
    if(pos != tokens.size())
      return ctx.fail("unsupported register operand");
    return true;
  }

  return parse_memory(tokens, 0, false, ctx, operand);
}

exprt asm_x86_semanticst::read(
  asm_lowering_contextt &ctx,
  const x86_operandt &operand,
  std::size_t width) const
{
  switch(operand.kind)
  {
  case x86_operandt::kindt::REGISTER:
    if(operand.offset == 0 && width == register_width())
      return operand.storage;
    return extract(operand.storage, operand.offset, width);

  case x86_operandt::kindt::IMMEDIATE:
    if(operand.value.type().id() == ID_integer)
    {
      return constant(
        numeric_cast_v<mp_integer>(to_constant_expr(operand.value)), width);
    }
    return typecast_exprt::conditional_cast(operand.value, bv(width));

  case x86_operandt::kindt::MEMORY:
    if(operand.environment)
      return ctx.nondet(bv(width));
    if(operand.lvalue.is_not_nil() && operand.natural_width == width)
      return ctx.to_bits(operand.lvalue, width);
    return ctx.memory(operand.address, width);
  }

  UNREACHABLE;
}

bool asm_x86_semanticst::write(
  asm_lowering_contextt &ctx,
  const x86_operandt &operand,
  std::size_t width,
  const exprt &value) const
{
  switch(operand.kind)
  {
  case x86_operandt::kindt::REGISTER:
  {
    const std::size_t full = register_width();
    if(width == 32 && x86_64 && operand.offset == 0)
    {
      // 32-bit writes zero the upper half
      ctx.assign(operand.storage, resize(resize(value, 32), full));
    }
    else
    {
      ctx.assign(
        operand.storage,
        replace_bits(operand.storage, full, operand.offset, width, value));
    }
    return true;
  }

  case x86_operandt::kindt::IMMEDIATE:
    return ctx.fail("write to an immediate");

  case x86_operandt::kindt::MEMORY:
    if(operand.environment)
      return true; // not visible to the C program
    if(operand.lvalue.is_not_nil() && operand.natural_width == width)
    {
      ctx.assign(
        operand.lvalue,
        ctx.from_bits(resize(value, width), operand.lvalue.type()));
    }
    else
      ctx.assign(ctx.memory(operand.address, width), resize(value, width));
    return true;
  }

  UNREACHABLE;
}

bool asm_x86_semanticst::lower(
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx) const
{
  const std::string &m = instruction.mnemonic;

  bool lock = false;
  for(const auto &prefix : instruction.prefixes)
  {
    if(prefix == "lock")
      lock = true;
    else if(prefix == "rep" && m == "nop")
    {
      // rep; nop is pause
    }
    else
      return ctx.fail("unsupported prefix " + prefix);
  }

  if(
    !x86_64 && !m.empty() &&
    (m.back() == 'q' || m == "cdqe" || m == "cqo" || m == "cqto" ||
     m == "movabs" || m == "movsxd"))
  {
    return ctx.fail("64-bit instruction in 32-bit mode");
  }

  std::vector<x86_operandt> operands;
  for(const auto &tokens : instruction.operands)
  {
    if(
      m.size() > 1 && m[0] == 'j' && tokens.size() == 1 &&
      (tokens[0].kind == asm_tokent::kindt::LOCAL_LABEL ||
       tokens[0].kind == asm_tokent::kindt::C_LABEL ||
       tokens[0].is_identifier()))
    {
      continue; // branch target, handled below
    }
    x86_operandt operand;
    if(!parse_operand(tokens, ctx, operand))
      return false;
    operands.push_back(operand);
  }

  if(lock)
  {
    bool has_memory = false;
    for(const auto &op : operands)
      has_memory |= op.kind == x86_operandt::kindt::MEMORY;
    if(!has_memory)
      return ctx.fail("lock prefix without memory operand");
    ctx.mark_atomic();
    ctx.fence(true, true, true, true, false);
  }

  // no-ops and environment instructions
  if(m == "nop" || m == "pause" || m == "cli" || m == "sti" || m == "hlt")
    return operands.empty() || m == "nop" ? true : ctx.fail("operands");

  if(m == "clc" || m == "stc" || m == "cmc")
  {
    const exprt cf = ctx.flag("cf");
    ctx.assign(
      cf,
      m == "clc"   ? exprt{false_exprt{}}
      : m == "stc" ? exprt{true_exprt{}}
                   : exprt{not_exprt{cf}});
    return true;
  }

  if(m == "rdtsc" || m == "rdtscp" || m == "rdmsr" || m == "cpuid")
  {
    std::vector<std::string> written = {"rax", "rdx"};
    if(m == "rdtscp")
      written.push_back("rcx");
    if(m == "cpuid")
      written = {"rax", "rbx", "rcx", "rdx"};
    for(const auto &r : written)
    {
      x86_operandt reg = named_register(ctx, r, 32);
      write(ctx, reg, 32, ctx.nondet(bv(32)));
    }
    return true;
  }

  if(m == "wrmsr")
    return true;

  if(m == "mfence" || m == "lfence" || m == "sfence")
  {
    if(!operands.empty())
      return ctx.fail("operands of " + m);
    ctx.call("__asm_" + m, {});
    return true;
  }

  if(m == "fstcw" || m == "fnstcw" || m == "fldcw")
  {
    if(
      operands.size() != 1 || operands[0].kind != x86_operandt::kindt::MEMORY ||
      operands[0].environment)
    {
      return ctx.fail("unsupported operand of " + m);
    }
    ctx.call("__asm_" + m, {operands[0].address});
    return true;
  }

  if(m == "cltq" || m == "cdqe" || m == "cwtl" || m == "cwde")
  {
    const std::size_t from = (m == "cltq" || m == "cdqe") ? 32 : 16;
    const x86_operandt acc = accumulator(ctx, 2 * from);
    write(
      ctx, acc, 2 * from, sign_extend(read(ctx, acc, from), from, 2 * from));
    return true;
  }

  if(m == "cltd" || m == "cdq" || m == "cqto" || m == "cqo")
  {
    const std::size_t w = (m == "cqto" || m == "cqo") ? 64 : 32;
    const x86_operandt acc = accumulator(ctx, w);
    const x86_operandt rdx = named_register(ctx, "rdx", w);
    write(
      ctx,
      rdx,
      w,
      if_exprt{msb(read(ctx, acc, w), w), constant(-1, w), constant(0, w)});
    return true;
  }

  // set<cc>, cmov<cc>, j<cc>
  if(m.compare(0, 3, "set") == 0 && condition_codes().count(m.substr(3)))
  {
    if(operands.size() != 1)
      return ctx.fail("set requires one operand");
    return write(
      ctx, operands[0], 8, bool_to_bv(condition(m.substr(3), ctx), 8));
  }

  if(m.compare(0, 4, "cmov") == 0)
  {
    std::string cc = m.substr(4);
    std::size_t suffix = 0;
    if(
      !condition_codes().count(cc) && !cc.empty() &&
      condition_codes().count(cc.substr(0, cc.size() - 1)))
    {
      suffix = suffix_width(cc.back());
      cc.pop_back();
    }
    if(!condition_codes().count(cc) || operands.size() != 2)
      return ctx.fail("unsupported " + m);
    const std::size_t w = operation_width(operands, suffix);
    if(w == 0)
      return ctx.fail("unknown operand size");
    return write(
      ctx,
      operands[1],
      w,
      if_exprt{
        condition(cc, ctx),
        read(ctx, operands[0], w),
        read(ctx, operands[1], w)});
  }

  if(m[0] == 'j')
  {
    if(instruction.operands.size() != 1 || instruction.operands[0].size() != 1)
      return ctx.fail("unsupported branch");
    const asm_tokent &target = instruction.operands[0][0];
    if(m == "jmp")
      return ctx.branch(target, true_exprt{});
    const std::string cc = m.substr(1);
    if(!condition_codes().count(cc))
      return ctx.fail("unsupported branch " + m);
    return ctx.branch(target, condition(cc, ctx));
  }

  // movz/movs with explicit sizes, e.g. movzbl, movslq
  if(
    m.size() == 6 &&
    (m.compare(0, 4, "movz") == 0 || m.compare(0, 4, "movs") == 0))
  {
    const std::size_t from = suffix_width(m[4]), to = suffix_width(m[5]);
    if(from != 0 && to != 0 && from < to && operands.size() == 2)
    {
      const exprt src = read(ctx, operands[0], from);
      return write(
        ctx,
        operands[1],
        to,
        m[3] == 'z' ? resize(src, to) : sign_extend(src, from, to));
    }
  }

  if((m == "movzx" || m == "movsx" || m == "movsxd") && operands.size() == 2)
  {
    const std::size_t from = operation_width({operands[0]}, 0),
                      to = operation_width({operands[1]}, 0);
    if(from == 0 || to == 0 || from >= to)
      return ctx.fail("unsupported " + m);
    const exprt src = read(ctx, operands[0], from);
    return write(
      ctx,
      operands[1],
      to,
      m == "movzx" ? resize(src, to) : sign_extend(src, from, to));
  }

  // instructions with an optional size suffix
  std::string base = m;
  std::size_t suffix = 0;
  if(!sized_mnemonics().count(base))
  {
    if(
      m.size() > 1 && suffix_width(m.back()) != 0 &&
      sized_mnemonics().count(m.substr(0, m.size() - 1)))
    {
      base = m.substr(0, m.size() - 1);
      suffix = suffix_width(m.back());
    }
    else
      return ctx.fail("unsupported instruction " + m);
  }

  if(suffix == 64 && !x86_64)
    return ctx.fail("64-bit operation on i386");

  // the size is that of the destination for shifts (whose count may be %cl)
  // and for in (whose port may be %dx)
  std::vector<x86_operandt> by_size = operands;
  if(
    base == "shl" || base == "sal" || base == "shr" || base == "sar" ||
    base == "rol" || base == "ror" || base == "in")
  {
    std::reverse(by_size.begin(), by_size.end());
  }
  const std::size_t width = operation_width(by_size, suffix);
  if(width == 0 && base != "lea")
    return ctx.fail(
      "cannot determine the operand size of '" + instruction.text + "'");

  if(base == "xchg")
  {
    // xchg with a memory operand is implicitly locked
    for(const auto &op : operands)
    {
      if(op.kind == x86_operandt::kindt::MEMORY && !lock)
      {
        ctx.mark_atomic();
        ctx.fence(true, true, true, true, false);
        break;
      }
    }
  }

  return lower_sized(base, width, operands, instruction, ctx);
}

bool asm_x86_semanticst::lower_sized(
  const std::string &base,
  std::size_t w,
  std::vector<x86_operandt> &ops,
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx) const
{
  auto expect = [&](std::size_t n)
  {
    if(ops.size() != n)
    {
      ctx.fail(
        "'" + instruction.text + "' requires " + std::to_string(n) +
        " operands");
      return false;
    }
    return true;
  };

  auto temp = [&](const exprt &value, const std::string &suffix)
  {
    const symbol_exprt t = ctx.temporary(value.type(), suffix);
    ctx.assign(t, value);
    return t;
  };

  const exprt cf = ctx.flag("cf");

  if(base == "mov" || base == "movabs")
  {
    if(!expect(2))
      return false;
    return write(ctx, ops[1], w, read(ctx, ops[0], w));
  }

  if(base == "lea")
  {
    if(
      !expect(2) || ops[0].kind != x86_operandt::kindt::MEMORY ||
      ops[0].environment || ops[1].kind != x86_operandt::kindt::REGISTER)
    {
      return ctx.fail("unsupported lea");
    }
    const std::size_t to = ops[1].width;
    const exprt address = typecast_exprt::conditional_cast(
      ops[0].address, pointer_type(char_type()));
    return write(
      ctx,
      ops[1],
      to,
      resize(typecast_exprt{address, bv(config.ansi_c.pointer_width)}, to));
  }

  if(
    base == "add" || base == "adc" || base == "sub" || base == "sbb" ||
    base == "cmp")
  {
    if(!expect(2))
      return false;
    const symbol_exprt src = temp(read(ctx, ops[0], w), "src");
    const symbol_exprt dst = temp(read(ctx, ops[1], w), "dst");
    const exprt carry_in =
      (base == "adc" || base == "sbb") ? bool_to_bv(cf, w) : constant(0, w);
    const bool is_add = base == "add" || base == "adc";
    const symbol_exprt result = temp(
      is_add ? exprt{plus_exprt{plus_exprt{dst, src}, carry_in}}
             : exprt{minus_exprt{minus_exprt{dst, src}, carry_in}},
      "result");
    ctx.assign(
      ctx.flag("of"),
      is_add ? overflow_add(dst, src, result, w)
             : overflow_sub(dst, src, result, w));
    ctx.assign(
      cf,
      is_add ? carry_add(dst, src, carry_in, w)
             : borrow_sub(dst, src, carry_in, w));
    set_result_flags(ctx, result, w);
    if(base == "cmp")
      return true;
    return write(ctx, ops[1], w, result);
  }

  if(base == "and" || base == "or" || base == "xor" || base == "test")
  {
    if(!expect(2))
      return false;
    const exprt src = read(ctx, ops[0], w), dst = read(ctx, ops[1], w);
    const symbol_exprt result = temp(
      base == "or"    ? exprt{bitor_exprt{dst, src}}
      : base == "xor" ? exprt{bitxor_exprt{dst, src}}
                      : exprt{bitand_exprt{dst, src}},
      "result");
    set_logic_flags(ctx, result, w);
    if(base == "test")
      return true;
    return write(ctx, ops[1], w, result);
  }

  if(base == "not")
  {
    if(!expect(1))
      return false;
    return write(ctx, ops[0], w, bitnot_exprt{read(ctx, ops[0], w)});
  }

  if(base == "neg")
  {
    if(!expect(1))
      return false;
    const symbol_exprt src = temp(read(ctx, ops[0], w), "src");
    const symbol_exprt result = temp(unary_minus_exprt{src}, "result");
    ctx.assign(cf, not_exprt{is_zero(src)});
    ctx.assign(ctx.flag("of"), equal_exprt{src, constant(power(2, w - 1), w)});
    set_result_flags(ctx, result, w);
    return write(ctx, ops[0], w, result);
  }

  if(base == "inc" || base == "dec")
  {
    if(!expect(1))
      return false;
    const symbol_exprt dst = temp(read(ctx, ops[0], w), "dst");
    const exprt one = constant(1, w);
    const symbol_exprt result = temp(
      base == "inc" ? exprt{plus_exprt{dst, one}}
                    : exprt{minus_exprt{dst, one}},
      "result");
    // CF is not affected
    ctx.assign(
      ctx.flag("of"),
      base == "inc" ? overflow_add(dst, one, result, w)
                    : overflow_sub(dst, one, result, w));
    set_result_flags(ctx, result, w);
    return write(ctx, ops[0], w, result);
  }

  if(
    base == "shl" || base == "sal" || base == "shr" || base == "sar" ||
    base == "rol" || base == "ror")
  {
    // count is an immediate or %cl; a single operand means a count of 1
    x86_operandt count_operand;
    x86_operandt *dst_operand;
    if(ops.size() == 1)
    {
      count_operand.kind = x86_operandt::kindt::IMMEDIATE;
      count_operand.value = from_integer(1, integer_typet{});
      dst_operand = &ops[0];
    }
    else if(ops.size() == 2)
    {
      count_operand = ops[0];
      dst_operand = &ops[1];
    }
    else
      return ctx.fail("unsupported shift");

    const std::size_t mask = w == 64 ? 63 : 31;
    const symbol_exprt count = temp(
      bitand_exprt{read(ctx, count_operand, 8), constant(mask, 8)}, "count");
    const symbol_exprt dst = temp(read(ctx, *dst_operand, w), "dst");
    const exprt count_w = resize(count, w);

    exprt result;
    exprt carry;
    if(base == "shl" || base == "sal")
    {
      result = shl_exprt{dst, count_w};
      // the last bit shifted out: bit w - count of the original
      carry = extractbit_exprt{
        lshr_exprt{dst, minus_exprt{constant(w, w), count_w}}, 0};
    }
    else if(base == "shr" || base == "sar")
    {
      result =
        base == "shr"
          ? exprt{lshr_exprt{dst, count_w}}
          : exprt{typecast_exprt{
              ashr_exprt{typecast_exprt{dst, signedbv_typet{w}}, count_w},
              bv(w)}};
      carry = extractbit_exprt{
        lshr_exprt{dst, minus_exprt{count_w, constant(1, w)}}, 0};
    }
    else
    {
      // rotates: the count is taken modulo the width
      const exprt n = bitand_exprt{count_w, constant(w - 1, w)};
      const exprt left =
        base == "rol" ? n : exprt{minus_exprt{constant(w, w), n}};
      const exprt right = minus_exprt{constant(w, w), left};
      result = if_exprt{
        is_zero(n),
        dst,
        bitor_exprt{shl_exprt{dst, left}, lshr_exprt{dst, right}}};
      carry = base == "rol" ? extractbit_exprt{result, 0} : msb(result, w);
    }

    const symbol_exprt res = temp(result, "result");
    const exprt changed = not_exprt{is_zero(count)};
    const bool beyond_possible = w < mask + 1;
    exprt new_carry = carry;
    if(beyond_possible && base != "rol" && base != "ror")
    {
      // counts larger than the width leave CF undefined
      new_carry = if_exprt{
        binary_relation_exprt{count, ID_gt, constant(w, 8)},
        ctx.nondet(bool_typet{}),
        carry};
    }
    ctx.assign(cf, if_exprt{changed, new_carry, cf});
    // OF is only defined for counts of 1
    exprt of_one;
    if(base == "shl" || base == "sal")
      of_one = notequal_exprt{msb(res, w), carry};
    else if(base == "shr")
      of_one = msb(dst, w);
    else if(base == "sar")
      of_one = false_exprt{};
    else if(base == "rol")
      of_one = notequal_exprt{msb(res, w), extractbit_exprt{res, 0}};
    else
      of_one = notequal_exprt{msb(res, w), extractbit_exprt{res, w - 2}};
    const exprt of = ctx.flag("of");
    ctx.assign(
      of,
      if_exprt{
        changed,
        if_exprt{
          equal_exprt{count, constant(1, 8)}, of_one, ctx.nondet(bool_typet{})},
        of});
    if(base != "rol" && base != "ror")
    {
      ctx.assign(
        ctx.flag("zf"), if_exprt{changed, is_zero(res), ctx.flag("zf")});
      ctx.assign(
        ctx.flag("sf"), if_exprt{changed, msb(res, w), ctx.flag("sf")});
      ctx.assign(
        ctx.flag("pf"),
        if_exprt{changed, even_parity_low_byte(res), ctx.flag("pf")});
    }
    return write(ctx, *dst_operand, w, res);
  }

  if(base == "bt" || base == "bts" || base == "btr" || base == "btc")
  {
    if(!expect(2))
      return false;

    x86_operandt target = ops[1];
    exprt bit;
    if(
      target.kind == x86_operandt::kindt::MEMORY &&
      ops[0].kind == x86_operandt::kindt::REGISTER)
    {
      if(target.environment)
        return ctx.fail("bit string operation on segment memory");
      // the bit offset addresses a bit string starting at the operand:
      // the word is at address + (offset >> log2(w)) * (w / 8)
      const std::size_t pw = config.ansi_c.pointer_width;
      const exprt offset = sign_extend(read(ctx, ops[0], w), w, pw);
      const std::size_t shift = w == 64 ? 6 : w == 32 ? 5 : 4;
      const exprt word_index = typecast_exprt{
        ashr_exprt{typecast_exprt{offset, signedbv_typet{pw}}, shift},
        signedbv_typet{pw}};
      const exprt byte_offset =
        mult_exprt{word_index, from_integer(w / 8, signedbv_typet{pw})};
      target.address = plus_exprt{
        typecast_exprt::conditional_cast(
          target.address, pointer_type(char_type())),
        byte_offset};
      target.lvalue = nil_exprt{};
      target.natural_width = 0;
      bit = resize(bitand_exprt{offset, constant(w - 1, pw)}, w);
    }
    else
      bit = bitand_exprt{read(ctx, ops[0], w), constant(w - 1, w)};

    const symbol_exprt b = temp(resize(bit, w), "bit");
    const symbol_exprt word = temp(read(ctx, target, w), "word");
    ctx.assign(cf, extractbit_exprt{lshr_exprt{word, b}, 0});
    undefined_flags(ctx, {"of", "sf", "pf"});
    if(base == "bt")
      return true;
    const exprt mask = shl_exprt{constant(1, w), b};
    const exprt result = base == "bts" ? exprt{bitor_exprt{word, mask}}
                         : base == "btr"
                           ? exprt{bitand_exprt{word, bitnot_exprt{mask}}}
                           : exprt{bitxor_exprt{word, mask}};
    return write(ctx, target, w, result);
  }

  if(base == "bsf" || base == "bsr" || base == "tzcnt" || base == "lzcnt")
  {
    if(!expect(2))
      return false;
    const symbol_exprt src = temp(read(ctx, ops[0], w), "src");
    const exprt zero_src = is_zero(src);
    if(base == "bsf" || base == "bsr")
    {
      const exprt index =
        base == "bsf" ? exprt{count_trailing_zeros_exprt{src, false, bv(w)}}
                      : exprt{minus_exprt{
                          constant(w - 1, w),
                          count_leading_zeros_exprt{src, false, bv(w)}}};
      ctx.assign(ctx.flag("zf"), zero_src);
      undefined_flags(ctx, {"cf", "of", "sf", "pf"});
      if(ops[1].kind != x86_operandt::kindt::REGISTER)
        return ctx.fail("unsupported destination of " + base);
      const auto nonzero = ctx.begin_conditional(not_exprt{zero_src});
      if(!write(ctx, ops[1], w, index))
        return false;
      ctx.end_conditional(nonzero);
      // For a zero source, the destination is undefined (Intel) or unchanged
      // (AMD), including the bits above a 32-bit destination: the whole
      // register may hold any value.
      const auto zero = ctx.begin_conditional(zero_src);
      ctx.assign(ops[1].storage, ctx.nondet(ops[1].storage.type()));
      ctx.end_conditional(zero);
      return true;
    }
    const symbol_exprt result = temp(
      base == "tzcnt" ? exprt{count_trailing_zeros_exprt{src, true, bv(w)}}
                      : exprt{count_leading_zeros_exprt{src, true, bv(w)}},
      "result");
    ctx.assign(cf, zero_src);
    ctx.assign(ctx.flag("zf"), is_zero(result));
    undefined_flags(ctx, {"of", "sf", "pf"});
    return write(ctx, ops[1], w, result);
  }

  if(base == "popcnt")
  {
    if(!expect(2))
      return false;
    const symbol_exprt src = temp(read(ctx, ops[0], w), "src");
    ctx.assign(ctx.flag("zf"), is_zero(src));
    ctx.assign(cf, false_exprt{});
    ctx.assign(ctx.flag("of"), false_exprt{});
    ctx.assign(ctx.flag("sf"), false_exprt{});
    ctx.assign(ctx.flag("pf"), false_exprt{});
    return write(ctx, ops[1], w, popcount_exprt{src, bv(w)});
  }

  if(base == "bswap")
  {
    if(!expect(1) || (w != 32 && w != 64))
      return ctx.fail("unsupported bswap");
    return write(ctx, ops[0], w, bswap_exprt{read(ctx, ops[0], w), 8});
  }

  if(base == "xchg")
  {
    if(!expect(2))
      return false;
    const symbol_exprt a = temp(read(ctx, ops[0], w), "a");
    const symbol_exprt b = temp(read(ctx, ops[1], w), "b");
    return write(ctx, ops[0], w, b) && write(ctx, ops[1], w, a);
  }

  if(base == "xadd")
  {
    if(!expect(2))
      return false;
    const symbol_exprt src = temp(read(ctx, ops[0], w), "src");
    const symbol_exprt dst = temp(read(ctx, ops[1], w), "dst");
    const symbol_exprt sum = temp(plus_exprt{dst, src}, "sum");
    ctx.assign(ctx.flag("of"), overflow_add(dst, src, sum, w));
    ctx.assign(cf, carry_add(dst, src, constant(0, w), w));
    set_result_flags(ctx, sum, w);
    return write(ctx, ops[0], w, dst) && write(ctx, ops[1], w, sum);
  }

  if(base == "cmpxchg")
  {
    if(!expect(2))
      return false;
    const x86_operandt acc = accumulator(ctx, w);
    const symbol_exprt src = temp(read(ctx, ops[0], w), "src");
    const symbol_exprt dst = temp(read(ctx, ops[1], w), "dst");
    const symbol_exprt expected = temp(read(ctx, acc, w), "expected");
    const symbol_exprt diff = temp(minus_exprt{expected, dst}, "diff");
    ctx.assign(ctx.flag("of"), overflow_sub(expected, dst, diff, w));
    ctx.assign(cf, borrow_sub(expected, dst, constant(0, w), w));
    set_result_flags(ctx, diff, w);
    const exprt equal = equal_exprt{expected, dst};
    // Only one of destination and accumulator is written: a 32-bit write
    // zero-extends a register, so writing the other one with its own value
    // would clear its upper bits.
    const auto success = ctx.begin_conditional(equal);
    if(!write(ctx, ops[1], w, src))
      return false;
    ctx.end_conditional(success);
    const auto failure = ctx.begin_conditional(not_exprt{equal});
    if(!write(ctx, acc, w, dst))
      return false;
    ctx.end_conditional(failure);
    return true;
  }

  if(base == "in")
  {
    if(ops.size() != 2)
      return ctx.fail("unsupported in");
    return write(ctx, ops[1], w, ctx.nondet(bv(w)));
  }

  if(base == "out")
    return ops.size() == 2 ? true : ctx.fail("unsupported out");

  return ctx.fail("unsupported instruction " + instruction.mnemonic);
}
} // namespace

std::unique_ptr<asm_semanticst> make_asm_x86_semantics(bool x86_64)
{
  return std::make_unique<asm_x86_semanticst>(x86_64);
}

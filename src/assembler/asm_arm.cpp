/*******************************************************************\

Module: Inline assembly: AArch32 instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Instruction semantics for AArch32 (A32 and T32 instruction sets, GNU
/// syntax)

#include "asm_arm.h"

#include <util/bitvector_expr.h>
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
using asm_bv::bv;
using asm_bv::constant;
using asm_bv::extract;
using asm_bv::is_zero;
using asm_bv::resize;
using asm_bv::sign_extend;

namespace
{
struct a32_operandt
{
  enum class kindt
  {
    REGISTER,
    IMMEDIATE,
    MEMORY,
    /// a coprocessor, system register, or other name, in `name`
    NAME
  };

  kindt kind = kindt::REGISTER;

  // REGISTER: storage (32 bits)
  exprt storage;

  // IMMEDIATE
  exprt value;

  // MEMORY: the address
  exprt address;
  /// for memory operands bound to a C lvalue: that lvalue and its width
  exprt lvalue;
  std::size_t natural_width = 0;

  // NAME (lower case)
  std::string name;
};

/// An instruction mnemonic split into its operation, the flag-setting `s`
/// suffix, and the condition
struct a32_mnemonict
{
  std::string base;
  bool sets_flags = false;
  std::string condition = "al";
};

/// The operations, longest first, so that, for example, `bics` is not read
/// as `b` with condition `ics`
const std::vector<std::string> &operations()
{
  static const std::vector<std::string> result = []
  {
    std::vector<std::string> b = {
      "mov",   "mvn",    "add",    "adc",   "sub",   "sbc",    "rsb",
      "and",   "orr",    "eor",    "bic",   "cmp",   "cmn",    "tst",
      "teq",   "lsl",    "lsr",    "asr",   "ror",   "neg",    "mul",
      "b",     "cbz",    "cbnz",   "ldr",   "ldrb",  "ldrh",   "ldrsb",
      "ldrsh", "str",    "strb",   "strh",  "ldrex", "ldrexb", "ldrexh",
      "strex", "strexb", "strexh", "clz",   "rev",   "rev16",  "rbit",
      "uxtb",  "uxth",   "sxtb",   "sxth",  "movw",  "movt",   "mrs",
      "msr",   "mrc",    "mcr",    "nop",   "yield", "wfe",    "wfi",
      "sev",   "sevl",   "push",   "pop",   "ldm",   "ldmia",  "ldmib",
      "ldmda", "ldmdb",  "ldmfd",  "ldmfa", "ldmed", "ldmea",  "stm",
      "stmia", "stmib",  "stmda",  "stmdb", "stmfd", "stmfa",  "stmed",
      "stmea"};
    std::stable_sort(
      b.begin(),
      b.end(),
      [](const std::string &x, const std::string &y)
      { return x.size() > y.size(); });
    return b;
  }();
  return result;
}

/// The operations that take an `s` suffix
const std::set<std::string> &flag_setting_operations()
{
  static const std::set<std::string> result = {
    "mov",
    "mvn",
    "add",
    "adc",
    "sub",
    "sbc",
    "rsb",
    "and",
    "orr",
    "eor",
    "bic",
    "lsl",
    "lsr",
    "asr",
    "ror",
    "neg",
    "mul"};
  return result;
}

/// Split \p m into operation, `s` suffix, and condition, in the order of
/// unified syntax (`addseq`) or of divided syntax (`addeqs`).
bool decode(const std::string &m, a32_mnemonict &result)
{
  for(const auto &base : operations())
  {
    if(m.compare(0, base.size(), base) != 0)
      continue;
    std::string rest = m.substr(base.size());
    bool s = false;
    if(flag_setting_operations().count(base) != 0)
    {
      if(!rest.empty() && rest.front() == 's')
      {
        s = true;
        rest.erase(0, 1);
      }
      else if(rest.size() == 3 && rest.back() == 's')
      {
        s = true;
        rest.pop_back();
      }
    }
    if(!rest.empty() && asm_arm::condition_codes().count(rest) == 0)
      continue;
    result.base = base;
    result.sets_flags = s;
    result.condition = rest.empty() ? "al" : rest;
    return true;
  }
  return false;
}

/// \return The canonical name of the general-purpose register \p raw, or the
///   empty string if \p raw is not one (`pc` is not modeled)
std::string canonical_a32_register(const std::string &raw)
{
  std::string name = raw;
  for(auto &c : name)
    c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));

  static const std::map<std::string, std::string> aliases = {
    {"sb", "r9"},
    {"sl", "r10"},
    {"fp", "r11"},
    {"ip", "r12"},
    {"sp", "r13"},
    {"lr", "r14"}};
  auto alias = aliases.find(name);
  if(alias != aliases.end())
    return alias->second;

  if(name.size() >= 2 && name.size() <= 3 && name[0] == 'r')
  {
    const std::string digits = name.substr(1);
    if(std::all_of(
         digits.begin(),
         digits.end(),
         [](char c) { return std::isdigit(static_cast<unsigned char>(c)); }))
    {
      const int n = std::stoi(digits);
      if(n <= 14 && std::to_string(n) == digits)
        return "r" + std::to_string(n);
    }
  }
  return {};
}

/// A load or store of multiple registers (ldm, stm, push, pop)
struct a32_multiplet
{
  bool load = false;
  /// the first address is the base (increment after), the base plus 4
  /// (increment before), or the base minus 4 times the number of registers
  /// plus 4 (decrement after) or without the plus 4 (decrement before)
  enum class modet
  {
    INCREMENT_AFTER,
    INCREMENT_BEFORE,
    DECREMENT_AFTER,
    DECREMENT_BEFORE
  } mode = modet::INCREMENT_AFTER;
  /// push and pop, which have the stack pointer as implicit base with
  /// writeback
  bool push_pop = false;
};

/// \return Whether \p base is a load or store of multiple registers, which
///   is then described by \p result.
bool multiple(const std::string &base, a32_multiplet &result)
{
  using modet = a32_multiplet::modet;
  static const std::map<std::string, std::pair<bool, modet>> forms = {
    {"ldm", {true, modet::INCREMENT_AFTER}},
    {"ldmia", {true, modet::INCREMENT_AFTER}},
    {"ldmfd", {true, modet::INCREMENT_AFTER}},
    {"ldmib", {true, modet::INCREMENT_BEFORE}},
    {"ldmed", {true, modet::INCREMENT_BEFORE}},
    {"ldmda", {true, modet::DECREMENT_AFTER}},
    {"ldmfa", {true, modet::DECREMENT_AFTER}},
    {"ldmdb", {true, modet::DECREMENT_BEFORE}},
    {"ldmea", {true, modet::DECREMENT_BEFORE}},
    {"stm", {false, modet::INCREMENT_AFTER}},
    {"stmia", {false, modet::INCREMENT_AFTER}},
    {"stmea", {false, modet::INCREMENT_AFTER}},
    {"stmib", {false, modet::INCREMENT_BEFORE}},
    {"stmfa", {false, modet::INCREMENT_BEFORE}},
    {"stmda", {false, modet::DECREMENT_AFTER}},
    {"stmed", {false, modet::DECREMENT_AFTER}},
    {"stmdb", {false, modet::DECREMENT_BEFORE}},
    {"stmfd", {false, modet::DECREMENT_BEFORE}},
    {"pop", {true, modet::INCREMENT_AFTER}},
    {"push", {false, modet::DECREMENT_BEFORE}}};
  auto it = forms.find(base);
  if(it == forms.end())
    return false;
  result.load = it->second.first;
  result.mode = it->second.second;
  result.push_pop = base == "push" || base == "pop";
  return true;
}

/// One register of a register list: its number (-1 for an operand
/// reference, whose register is not known) and its tokens
struct a32_list_entryt
{
  int number;
  asm_token_listt tokens;
};

/// Parse the register list \p tokens (`{r4, r6-r8}`).
/// \return false if \p tokens is not a register list
bool register_list(
  const asm_token_listt &tokens,
  std::vector<a32_list_entryt> &entries)
{
  if(
    tokens.size() < 3 || !tokens.front().is_punctuation('{') ||
    !tokens.back().is_punctuation('}'))
  {
    return false;
  }
  auto number = [](const asm_tokent &token)
  {
    if(!token.is_identifier())
      return -1;
    const std::string canonical = canonical_a32_register(token.text);
    return canonical.empty() ? -1 : std::stoi(canonical.substr(1));
  };
  for(std::size_t i = 1; i + 1 < tokens.size(); ++i)
  {
    const asm_tokent &token = tokens[i];
    if(token.is_punctuation(','))
      continue;
    if(token.kind == asm_tokent::kindt::OPERAND)
    {
      entries.push_back({-1, {token}});
      continue;
    }
    const int first = number(token);
    if(first < 0)
      return false;
    if(i + 2 < tokens.size() - 1 && tokens[i + 1].is_punctuation('-'))
    {
      // a range rA-rB
      const int last = number(tokens[i + 2]);
      if(last < first)
        return false;
      for(int n = first; n <= last; ++n)
      {
        entries.push_back(
          {n, {{asm_tokent::kindt::IDENTIFIER, "r" + std::to_string(n)}}});
      }
      i += 2;
    }
    else
      entries.push_back({first, {token}});
  }
  return !entries.empty();
}

/// What the instruction semantics need to know about the statement as a
/// whole
class a32_statet : public asm_semantics_statet
{
public:
  /// Whether the statement may be in divided syntax for a Thumb-1 target
  /// (see \ref make_a32_state)
  bool maybe_thumb1_divided = true;
  /// If not empty, why the statement is not modeled
  std::string failure;
  /// The registers pushed by push (and stmdb sp!) and not yet popped, the top
  /// (lowest address) last. The stack memory below the stack pointer belongs
  /// to no C object, so a statement whose pushes and pops are balanced in
  /// straight-line code (see \ref make_a32_state) can keep them here.
  std::vector<symbol_exprt> stack;
};

/// The fields of the special register \p target of `msr`.
/// \param target: the special register, in lower case, e.g. `cpsr_fc`
/// \param [out] known: whether \p target is understood, and writing it has
///   no effect on the modeled state other than on \p flags
/// \param [out] flags: whether the write sets the condition flags
/// \param [out] control: whether the write sets the control field (the
///   interrupt masks and the processor mode)
void msr_fields(
  const std::string &target,
  bool &known,
  bool &flags,
  bool &control)
{
  known = true;
  flags = control = false;
  if(target == "cpsr") // cpsr_fc
  {
    flags = control = true;
    return;
  }
  if(target == "apsr_nzcvq" || target == "apsr_nzcvqg" || target == "apsr_nzcv")
  {
    flags = true;
    return;
  }
  if(target == "apsr_g")
    return;
  if(target.compare(0, 5, "cpsr_") == 0 && target.size() > 5)
  {
    for(std::size_t i = 5; i < target.size(); ++i)
    {
      switch(target[i])
      {
      case 'f':
        flags = true;
        break;
      case 'c':
        control = true;
        break;
      case 's':
        // the GE flags, which are not modeled
        break;
      default:
        // the x field includes the endianness of data accesses
        known = false;
        return;
      }
    }
    return;
  }
  known = false;
}

/// \return Whether \p instruction, a load or store of multiple registers
///   of the form \p form, pushes registers to or pops them from the stack:
///   push, pop, or stmdb/stmfd (ldmia/ldmfd) of sp with writeback.
bool is_stack_operation(
  const asm_instructiont &instruction,
  const a32_multiplet &form)
{
  if(form.push_pop)
    return instruction.operands.size() == 1;
  using modet = a32_multiplet::modet;
  return instruction.operands.size() == 2 &&
         instruction.operands[0].size() == 2 &&
         instruction.operands[0][0].is_identifier() &&
         canonical_a32_register(instruction.operands[0][0].text) == "r13" &&
         instruction.operands[0][1].is_punctuation('!') &&
         (form.load ? form.mode == modet::INCREMENT_AFTER
                    : form.mode == modet::DECREMENT_BEFORE);
}

/// The statement-wide properties of \p instructions:
/// - In divided syntax, which GCC uses for inline assembly in A32 code and
///   for Thumb-1 targets, Thumb-1 data-processing instructions without an `s`
///   suffix may set the flags (`add r0, r1, r2` is `adds`). The statement is
///   known not to be such code if it starts with `.syntax unified`, or if it
///   uses an instruction or form that Thumb-1 does not have.
/// - `msr` of the control field may change the processor mode, and with it
///   the registers r8 to r14 that are named, which is not modeled.
/// - push and pop (and stmdb/ldmia of sp with writeback) are modeled with a
///   stack of their own (\ref a32_statet::stack), which requires the pushes
///   and pops to be balanced, unconditional, and in straight-line code: no
///   label or branch while registers are pushed.
std::unique_ptr<a32_statet>
make_a32_state(const std::vector<asm_instructiont> &instructions)
{
  auto state = std::make_unique<a32_statet>();

  static const std::set<std::string> not_thumb1 = {
    "teq",
    "clz",
    "rbit",
    "movw",
    "movt",
    "cbz",
    "cbnz",
    "ldrex",
    "ldrexb",
    "ldrexh",
    "strex",
    "strexb",
    "strexh",
    "mrc",
    "mcr",
    // Thumb-1 has only the increment-after forms of ldm and stm
    "ldmib",
    "ldmed",
    "ldmda",
    "ldmfa",
    "ldmdb",
    "ldmea",
    "stmib",
    "stmfa",
    "stmda",
    "stmed",
    "stmdb",
    "stmfd"};

  bool unified_at_start = false, before_first_instruction = true;
  bool divided = false, changes_mode = false, names_banked = false;
  // the number of registers pushed
  std::size_t depth = 0;
  std::string stack_failure;
  for(const auto &instruction : instructions)
  {
    const std::string &m = instruction.mnemonic;
    if(depth != 0 && !instruction.labels.empty())
      stack_failure = "label while registers are pushed";
    if(m == ".syntax")
    {
      const bool unified = instruction.operands.size() == 1 &&
                           instruction.operands[0].size() == 1 &&
                           instruction.operands[0][0].text == "unified";
      if(unified && before_first_instruction)
        unified_at_start = true;
      if(!unified)
        divided = true;
      continue;
    }
    if(m.empty() || instruction.is_directive())
      continue;
    before_first_instruction = false;

    for(const auto &operand : instruction.operands)
    {
      for(const auto &token : operand)
      {
        if(!token.is_identifier())
          continue;
        const std::string reg = canonical_a32_register(token.text);
        if(!reg.empty() && std::stoi(reg.substr(1)) >= 8)
          names_banked = true;
      }
    }

    if(
      m.size() >= 2 && m.size() <= 5 && m[0] == 'i' && m[1] == 't' &&
      std::all_of(
        m.begin() + 2, m.end(), [](char c) { return c == 't' || c == 'e'; }))
    {
      state->maybe_thumb1_divided = false;
      continue;
    }

    a32_mnemonict decoded;
    if(!decode(m, decoded))
      continue;

    if(
      depth != 0 &&
      (decoded.base == "b" || decoded.base == "cbz" || decoded.base == "cbnz"))
    {
      stack_failure = "branch while registers are pushed";
    }
    a32_multiplet form;
    const bool stack_operation =
      multiple(decoded.base, form) && is_stack_operation(instruction, form);
    if(depth != 0 && !stack_operation)
    {
      // push and pop do not change the stack pointer in the model
      for(const auto &operand : instruction.operands)
      {
        for(const auto &token : operand)
        {
          if(
            token.is_identifier() &&
            canonical_a32_register(token.text) == "r13")
          {
            stack_failure = "sp used while registers are pushed";
          }
        }
      }
    }
    if(stack_operation)
    {
      std::vector<a32_list_entryt> entries;
      if(
        decoded.condition != "al" ||
        !register_list(instruction.operands.back(), entries))
      {
        stack_failure =
          "push or pop that is conditional or of registers that are not "
          "modeled (such as pc)";
      }
      else if(!form.load)
        depth += entries.size();
      else if(entries.size() > depth)
        stack_failure = "pop of registers that were not pushed";
      else
        depth -= entries.size();
    }

    if(
      not_thumb1.count(decoded.base) != 0 ||
      (decoded.condition != "al" && decoded.base != "b") ||
      (decoded.sets_flags && decoded.base != "mov"))
    {
      state->maybe_thumb1_divided = false;
    }

    if(
      decoded.base == "msr" && !instruction.operands.empty() &&
      instruction.operands[0].size() == 1)
    {
      std::string target = instruction.operands[0][0].text;
      for(auto &c : target)
        c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
      bool known, flags, control;
      msr_fields(target, known, flags, control);
      if(!known || control)
        changes_mode = true;
    }
  }

  if(unified_at_start && !divided)
    state->maybe_thumb1_divided = false;

  if(changes_mode && names_banked)
  {
    state->failure =
      "msr of the processor mode with named registers r8 to r14, which may be "
      "banked";
  }
  else if(depth != 0)
    state->failure = "registers pushed and not popped";
  else if(!stack_failure.empty())
    state->failure = stack_failure;

  return state;
}

class asm_arm_semanticst : public asm_semanticst
{
public:
  asm_arm_semanticst()
  {
    syntax_conventions.line_comments = {"@"};
    syntax_conventions.separators = ";";
  }

  std::string name() const override
  {
    return "AArch32";
  }

  const asm_syntaxt &syntax() const override
  {
    return syntax_conventions;
  }

  std::size_t register_width() const override
  {
    return 32;
  }

  std::string canonical_register(const std::string &name) const override
  {
    return canonical_a32_register(name);
  }

  bool reference_widens(const std::string &, std::size_t natural_width)
    const override
  {
    // references read the full register
    return natural_width < 32;
  }

  constraint_classt classify_constraint(
    const std::string &constraint,
    std::size_t &pos,
    std::string &) const override
  {
    switch(constraint[pos])
    {
    case 'l': // r0 to r7
    case 'h': // r8 to r15 (Thumb-1)
      return constraint_classt::REGISTER;
    case 'Q':
      return constraint_classt::MEMORY;
    case 'U':
      // Uv, Uy, Uq, ...: memory operands for particular instructions
      if(pos + 1 < constraint.size())
      {
        ++pos;
        return constraint_classt::MEMORY;
      }
      return constraint_classt::UNKNOWN;
    case 'I':
    case 'J':
    case 'K':
    case 'L':
    case 'M':
    case 'N':
    case 'O':
      return constraint_classt::IMMEDIATE;
    case 'P':
      if(pos + 1 < constraint.size())
      {
        ++pos;
        return constraint_classt::IMMEDIATE;
      }
      return constraint_classt::UNKNOWN;
    default:
      // k (the stack pointer), t, w, x (floating-point and vector
      // registers), ...: not modeled
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

  std::unique_ptr<asm_semantics_statet>
  make_state(const std::vector<asm_instructiont> &instructions) const override
  {
    return make_a32_state(instructions);
  }

protected:
  asm_syntaxt syntax_conventions;

  bool parse_operand(
    const asm_token_listt &tokens,
    asm_lowering_contextt &ctx,
    a32_operandt &operand) const;

  exprt read(
    asm_lowering_contextt &ctx,
    const a32_operandt &operand,
    std::size_t width) const;

  bool write(
    asm_lowering_contextt &ctx,
    const a32_operandt &operand,
    std::size_t width,
    const exprt &value) const;

  bool lower_operation(
    const a32_mnemonict &decoded,
    std::vector<a32_operandt> &ops,
    const asm_instructiont &instruction,
    asm_lowering_contextt &ctx) const;

  bool lower_memory(
    const a32_mnemonict &decoded,
    std::vector<a32_operandt> &ops,
    const asm_instructiont &instruction,
    asm_lowering_contextt &ctx) const;

  bool lower_system(
    const a32_mnemonict &decoded,
    std::vector<a32_operandt> &ops,
    asm_lowering_contextt &ctx) const;

  /// Parse the register list \p tokens into \p registers, in ascending
  /// order of register numbers (which is the order in memory).
  /// \return false if the list is not modeled
  bool parse_register_list(
    const asm_token_listt &tokens,
    asm_lowering_contextt &ctx,
    std::vector<a32_operandt> &registers,
    std::vector<std::string> &canonical) const;

  bool lower_multiple(
    const a32_multiplet &form,
    const asm_instructiont &instruction,
    const a32_statet &state,
    asm_lowering_contextt &ctx) const;

  bool lower_stack(
    const a32_multiplet &form,
    const asm_instructiont &instruction,
    a32_statet &state,
    asm_lowering_contextt &ctx) const;
};

bool asm_arm_semanticst::parse_operand(
  const asm_token_listt &tokens,
  asm_lowering_contextt &ctx,
  a32_operandt &operand) const
{
  if(tokens.empty())
    return ctx.fail("empty operand");

  const asm_tokent &first = tokens[0];

  // immediate: #n, #-n, n, #%N
  if(
    first.is_punctuation('#') || first.kind == asm_tokent::kindt::NUMBER ||
    first.is_punctuation('-'))
  {
    std::size_t pos = first.is_punctuation('#') ? 1 : 0;
    bool negative = false;
    if(pos < tokens.size() && tokens[pos].is_punctuation('-'))
    {
      negative = true;
      ++pos;
    }
    if(pos + 1 != tokens.size())
      return ctx.fail("unsupported immediate");
    operand.kind = a32_operandt::kindt::IMMEDIATE;
    const asm_tokent &token = tokens[pos];
    if(token.kind == asm_tokent::kindt::NUMBER)
    {
      operand.value =
        from_integer(negative ? -token.number : token.number, integer_typet{});
      return true;
    }
    if(
      token.kind == asm_tokent::kindt::OPERAND && token.modifier.empty() &&
      ctx.operands.operands.at(token.index).kind ==
        asm_operandt::kindt::IMMEDIATE)
    {
      operand.value = ctx.operand_immediate(token.index);
      if(negative)
        operand.value = unary_minus_exprt{operand.value};
      return true;
    }
    return ctx.fail("unsupported immediate");
  }

  // memory: [Rn], [Rn, #imm], [Rn, Rm]
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
    a32_operandt base;
    if(
      !parse_operand(parts[0], ctx, base) ||
      base.kind != a32_operandt::kindt::REGISTER)
    {
      return ctx.fail("unsupported base register");
    }
    exprt address = typecast_exprt{
      resize(read(ctx, base, 32), config.ansi_c.pointer_width),
      pointer_type(char_type())};
    if(parts.size() == 2)
    {
      a32_operandt offset;
      if(!parse_operand(parts[1], ctx, offset))
        return false;
      if(offset.kind == a32_operandt::kindt::IMMEDIATE)
      {
        address = plus_exprt{
          address,
          typecast_exprt::conditional_cast(
            offset.value, signedbv_typet{config.ansi_c.pointer_width})};
      }
      else if(offset.kind == a32_operandt::kindt::REGISTER)
      {
        address = plus_exprt{
          address,
          typecast_exprt{
            resize(read(ctx, offset, 32), config.ansi_c.pointer_width),
            signedbv_typet{config.ansi_c.pointer_width}}};
      }
      else
        return ctx.fail("unsupported offset");
    }
    else if(parts.size() > 2)
      return ctx.fail("unsupported addressing mode");
    operand.kind = a32_operandt::kindt::MEMORY;
    operand.address = address;
    return true;
  }

  if(tokens.size() == 1 && first.kind == asm_tokent::kindt::OPERAND)
  {
    if(!first.modifier.empty())
      return ctx.fail("unsupported operand modifier %" + first.modifier);
    const asm_operandt &bound = ctx.operands.operands.at(first.index);
    switch(bound.kind)
    {
    case asm_operandt::kindt::REGISTER:
      operand.kind = a32_operandt::kindt::REGISTER;
      operand.storage = ctx.operand_storage(first.index);
      return true;
    case asm_operandt::kindt::MEMORY:
      operand.kind = a32_operandt::kindt::MEMORY;
      operand.address = ctx.operand_address(first.index);
      operand.lvalue = dereference_exprt{ctx.operand_address(first.index)};
      operand.natural_width = ctx.operand_width(first.index);
      return true;
    case asm_operandt::kindt::IMMEDIATE:
      operand.kind = a32_operandt::kindt::IMMEDIATE;
      operand.value = ctx.operand_immediate(first.index);
      return true;
    case asm_operandt::kindt::FLAG_OUTPUT:
      break;
    }
    return ctx.fail("flag output used in template");
  }

  if(tokens.size() == 1 && first.is_identifier())
  {
    const std::string reg = canonical_a32_register(first.text);
    if(!reg.empty())
    {
      operand.kind = a32_operandt::kindt::REGISTER;
      operand.storage = ctx.hardware_register(reg);
      return true;
    }
    operand.kind = a32_operandt::kindt::NAME;
    operand.name = first.text;
    for(auto &c : operand.name)
      c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    return true;
  }

  return ctx.fail("unsupported operand");
}

exprt asm_arm_semanticst::read(
  asm_lowering_contextt &ctx,
  const a32_operandt &operand,
  std::size_t width) const
{
  switch(operand.kind)
  {
  case a32_operandt::kindt::REGISTER:
    return width == 32 ? operand.storage : extract(operand.storage, 0, width);

  case a32_operandt::kindt::IMMEDIATE:
    if(operand.value.type().id() == ID_integer)
    {
      return constant(
        numeric_cast_v<mp_integer>(to_constant_expr(operand.value)), width);
    }
    return typecast_exprt::conditional_cast(operand.value, bv(width));

  case a32_operandt::kindt::MEMORY:
    if(ctx.exclusive_open())
    {
      ctx.fail("memory access between load-exclusive and store-exclusive");
      return ctx.nondet(bv(width));
    }
    if(operand.lvalue.is_not_nil() && operand.natural_width == width)
      return ctx.to_bits(operand.lvalue, width);
    return ctx.memory(operand.address, width);

  case a32_operandt::kindt::NAME:
    break;
  }

  // includes pc, whose value is the address of the instruction
  ctx.fail("unsupported operand " + operand.name);
  return ctx.nondet(bv(width));
}

bool asm_arm_semanticst::write(
  asm_lowering_contextt &ctx,
  const a32_operandt &operand,
  std::size_t width,
  const exprt &value) const
{
  switch(operand.kind)
  {
  case a32_operandt::kindt::REGISTER:
    ctx.assign(operand.storage, resize(resize(value, width), 32));
    return true;

  case a32_operandt::kindt::MEMORY:
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

  case a32_operandt::kindt::IMMEDIATE:
  case a32_operandt::kindt::NAME:
    break;
  }

  // includes pc, a write to which is a branch
  return ctx.fail("invalid destination " + operand.name);
}

bool asm_arm_semanticst::lower(
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx) const
{
  auto *state = dynamic_cast<a32_statet *>(ctx.semantics_state.get());
  INVARIANT(state != nullptr, "the state is created by make_state");
  if(!state->failure.empty())
    return ctx.fail(state->failure);

  std::string m = instruction.mnemonic;

  if(!instruction.prefixes.empty())
    return ctx.fail("unexpected prefix");

  // the width qualifiers of unified syntax select an encoding
  if(
    m.size() > 2 && (m.compare(m.size() - 2, 2, ".n") == 0 ||
                     m.compare(m.size() - 2, 2, ".w") == 0))
  {
    m.erase(m.size() - 2);
  }

  // An IT block makes the next (up to four) instructions conditional. Each
  // of these carries its condition as a suffix, which the assemblers check
  // against the IT instruction, so that the IT instruction itself has no
  // further effect.
  if(
    m.size() >= 2 && m.size() <= 5 && m[0] == 'i' && m[1] == 't' &&
    std::all_of(
      m.begin() + 2, m.end(), [](char c) { return c == 't' || c == 'e'; }))
  {
    if(
      instruction.operands.size() != 1 || instruction.operands[0].size() != 1 ||
      !instruction.operands[0][0].is_identifier())
    {
      return ctx.fail("unsupported " + m);
    }
    std::string condition = instruction.operands[0][0].text;
    for(auto &c : condition)
      c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    if(asm_arm::condition_codes().count(condition) == 0)
      return ctx.fail("unsupported " + m);
    return true;
  }

  // interrupt masks, which have no effect on the C program state; with a
  // mode operand, they change the processor mode, which is not modeled
  if(m == "cpsid" || m == "cpsie")
  {
    if(
      instruction.operands.size() != 1 || instruction.operands[0].size() != 1 ||
      !instruction.operands[0][0].is_identifier())
    {
      return ctx.fail("unsupported operands of " + m);
    }
    return true;
  }

  // preload hints do not access memory
  if(m == "pld" || m == "pldw" || m == "pli")
    return true;

  if(m == "clrex")
  {
    ctx.clear_exclusive();
    return true;
  }

  if(m == "dmb" || m == "dsb" || m == "isb")
    return asm_arm::lower_barrier(m, instruction, ctx);

  a32_mnemonict decoded;
  if(!decode(m, decoded))
    return ctx.fail("unsupported instruction " + m);

  // branches: the target is the last operand
  if(decoded.base == "b" || decoded.base == "cbz" || decoded.base == "cbnz")
  {
    if(instruction.operands.empty() || instruction.operands.back().size() != 1)
      return ctx.fail("unsupported branch target");
    const asm_tokent &target = instruction.operands.back().back();
    if(decoded.base == "b")
    {
      if(instruction.operands.size() != 1)
        return ctx.fail("unsupported branch");
      return ctx.retry_branch(
        target, asm_arm::condition(decoded.condition, ctx));
    }
    a32_operandt reg;
    if(
      instruction.operands.size() != 2 || decoded.condition != "al" ||
      !parse_operand(instruction.operands[0], ctx, reg) ||
      reg.kind != a32_operandt::kindt::REGISTER)
    {
      return ctx.fail("unsupported " + decoded.base);
    }
    const exprt zero = is_zero(read(ctx, reg, 32));
    return ctx.retry_branch(
      target, decoded.base == "cbz" ? zero : exprt{not_exprt{zero}});
  }

  // The compiler may address a memory operand relative to sp, which push and
  // pop do not change in the model.
  if(!state->stack.empty())
  {
    for(const auto &operand : instruction.operands)
    {
      for(const auto &token : operand)
      {
        if(
          token.kind == asm_tokent::kindt::OPERAND &&
          ctx.operands.operands.at(token.index).kind ==
            asm_operandt::kindt::MEMORY)
        {
          return ctx.fail("memory operand used while registers are pushed");
        }
      }
    }
  }

  a32_multiplet form;
  if(multiple(decoded.base, form))
  {
    if(is_stack_operation(instruction, form))
      return lower_stack(form, instruction, *state, ctx);
    if(decoded.condition == "al")
      return lower_multiple(form, instruction, *state, ctx);
    const auto skip =
      ctx.begin_conditional(asm_arm::condition(decoded.condition, ctx));
    if(!lower_multiple(form, instruction, *state, ctx))
      return false;
    ctx.end_conditional(skip);
    return true;
  }

  std::vector<a32_operandt> ops;
  for(const auto &tokens : instruction.operands)
  {
    a32_operandt op;
    if(!parse_operand(tokens, ctx, op))
      return false;
    ops.push_back(op);
  }

  if(decoded.condition == "al")
  {
    if(!lower_operation(decoded, ops, instruction, ctx))
      return false;

    // In divided syntax for Thumb-1, data-processing instructions without
    // an `s` suffix may set the flags (depending on the registers).
    if(
      state->maybe_thumb1_divided && !decoded.sets_flags &&
      flag_setting_operations().count(decoded.base) != 0)
    {
      for(const char *f : {"n", "z", "c", "v"})
        ctx.assign(ctx.flag(f), ctx.nondet(bool_typet{}));
    }
    return true;
  }

  // conditional execution
  const auto skip =
    ctx.begin_conditional(asm_arm::condition(decoded.condition, ctx));
  if(!lower_operation(decoded, ops, instruction, ctx))
    return false;
  ctx.end_conditional(skip);
  return true;
}

bool asm_arm_semanticst::lower_operation(
  const a32_mnemonict &decoded,
  std::vector<a32_operandt> &ops,
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx) const
{
  const std::string &b = decoded.base;

  auto is_reg = [&](std::size_t i)
  { return i < ops.size() && ops[i].kind == a32_operandt::kindt::REGISTER; };
  // a register or an immediate: the flexible second operand
  auto is_value = [&](std::size_t i)
  {
    return i < ops.size() && (ops[i].kind == a32_operandt::kindt::REGISTER ||
                              ops[i].kind == a32_operandt::kindt::IMMEDIATE);
  };
  auto temp = [&](const exprt &value, const std::string &suffix)
  {
    const symbol_exprt t = ctx.temporary(value.type(), suffix);
    ctx.assign(t, value);
    return t;
  };
  // the carry out of the shifter for an immediate depends on its encoding
  auto nondet_carry = [&]()
  { ctx.assign(ctx.flag("c"), ctx.nondet(bool_typet{})); };

  if(
    b == "nop" || b == "yield" || b == "wfe" || b == "wfi" || b == "sev" ||
    b == "sevl")
  {
    return true;
  }

  if(b == "mrs" || b == "msr" || b == "mrc" || b == "mcr")
    return lower_system(decoded, ops, ctx);

  if(b == "mov" || b == "mvn")
  {
    if(ops.size() != 2 || !is_reg(0) || !is_value(1))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    const symbol_exprt v = temp(read(ctx, ops[1], 32), "v");
    const symbol_exprt r = b == "mvn" ? temp(bitnot_exprt{v}, "r") : v;
    if(decoded.sets_flags)
    {
      asm_arm::set_nz(ctx, r, 32);
      if(ops[1].kind == a32_operandt::kindt::IMMEDIATE)
        nondet_carry();
    }
    return write(ctx, ops[0], 32, r);
  }

  if(b == "movw" || b == "movt")
  {
    if(
      ops.size() != 2 || !is_reg(0) ||
      ops[1].kind != a32_operandt::kindt::IMMEDIATE)
    {
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    }
    const exprt imm = read(ctx, ops[1], 16);
    if(b == "movw")
      return write(ctx, ops[0], 32, resize(imm, 32));
    return write(
      ctx,
      ops[0],
      32,
      concatenation_exprt{imm, extract(read(ctx, ops[0], 32), 0, 16), bv(32)});
  }

  static const std::set<std::string> unary = {
    "neg", "clz", "rev", "rev16", "rbit", "uxtb", "uxth", "sxtb", "sxth"};
  if(unary.count(b) != 0)
  {
    if(ops.size() != 2 || !is_reg(0) || !is_reg(1))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    const symbol_exprt v = temp(read(ctx, ops[1], 32), "v");
    exprt r;
    if(b == "neg")
      r = unary_minus_exprt{v};
    else if(b == "clz")
      r = count_leading_zeros_exprt{v, true, bv(32)};
    else if(b == "rev")
      r = bswap_exprt{v, 8};
    else if(b == "rev16")
    {
      r = bitor_exprt{
        bitand_exprt{lshr_exprt{v, 8}, constant(0x00ff00ff, 32)},
        bitand_exprt{shl_exprt{v, 8}, constant(0xff00ff00, 32)}};
    }
    else if(b == "rbit")
      r = bitreverse_exprt{v};
    else if(b == "uxtb" || b == "uxth")
      r = resize(extract(v, 0, b == "uxtb" ? 8 : 16), 32);
    else
      r = sign_extend(v, b == "sxtb" ? 8 : 16, 32);
    const symbol_exprt result = temp(r, "r");
    if(decoded.sets_flags) // negs
      asm_arm::set_sub_flags(ctx, constant(0, 32), v, result, 32);
    return write(ctx, ops[0], 32, result);
  }

  if(b == "mul")
  {
    // two-operand form: Rd, Rm means Rd, Rd, Rm
    if(ops.size() == 2)
      ops.insert(ops.begin() + 1, ops[0]);
    if(ops.size() != 3 || !is_reg(0) || !is_reg(1) || !is_reg(2))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    const symbol_exprt result =
      temp(mult_exprt{read(ctx, ops[1], 32), read(ctx, ops[2], 32)}, "r");
    if(decoded.sets_flags)
    {
      // C is unchanged from ARMv5 on, but unpredictable before
      asm_arm::set_nz(ctx, result, 32);
      nondet_carry();
    }
    return write(ctx, ops[0], 32, result);
  }

  static const std::set<std::string> binary = {
    "add",
    "adc",
    "sub",
    "sbc",
    "rsb",
    "and",
    "orr",
    "eor",
    "bic",
    "lsl",
    "lsr",
    "asr",
    "ror"};

  if(binary.count(b) != 0)
  {
    // two-operand form: Rd, Op2 means Rd, Rd, Op2
    if(ops.size() == 2)
      ops.insert(ops.begin() + 1, ops[0]);
    if(ops.size() != 3 || !is_reg(0) || !is_reg(1) || !is_value(2))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);

    const symbol_exprt x = temp(read(ctx, ops[1], 32), "a");
    const symbol_exprt y = temp(read(ctx, ops[2], 32), "b");
    const exprt carry = bool_to_bv(ctx.flag("c"), 32);
    exprt r;
    if(b == "add")
      r = plus_exprt{x, y};
    else if(b == "adc")
      r = plus_exprt{plus_exprt{x, y}, carry};
    else if(b == "sub")
      r = minus_exprt{x, y};
    else if(b == "sbc") // x - y - !C
      r = minus_exprt{minus_exprt{x, y}, minus_exprt{constant(1, 32), carry}};
    else if(b == "rsb")
      r = minus_exprt{y, x};
    else if(b == "and")
      r = bitand_exprt{x, y};
    else if(b == "orr")
      r = bitor_exprt{x, y};
    else if(b == "eor")
      r = bitxor_exprt{x, y};
    else if(b == "bic")
      r = bitand_exprt{x, bitnot_exprt{y}};
    else
    {
      // A shift by a register uses its bottom byte; shifts by 32 or more
      // yield 0 (or the sign for asr). An immediate is 0 to 32.
      const exprt n = bitand_exprt{y, constant(255, 32)};
      const exprt big = binary_relation_exprt{n, ID_ge, constant(32, 32)};
      if(b == "lsl")
        r = if_exprt{big, constant(0, 32), shl_exprt{x, n}};
      else if(b == "lsr")
        r = if_exprt{big, constant(0, 32), lshr_exprt{x, n}};
      else if(b == "asr")
      {
        r = typecast_exprt{
          ashr_exprt{
            typecast_exprt{x, signedbv_typet{32}},
            if_exprt{big, constant(31, 32), n}},
          bv(32)};
      }
      else
      {
        const exprt k = bitand_exprt{n, constant(31, 32)};
        r = if_exprt{
          is_zero(k),
          x,
          bitor_exprt{
            lshr_exprt{x, k}, shl_exprt{x, minus_exprt{constant(32, 32), k}}}};
      }
    }

    const symbol_exprt result = temp(r, "r");
    if(decoded.sets_flags)
    {
      if(b == "add")
        asm_arm::set_add_flags(ctx, x, y, constant(0, 32), result, 32);
      else if(b == "adc")
        asm_arm::set_add_flags(ctx, x, y, carry, result, 32);
      else if(b == "sub")
        asm_arm::set_sub_flags(ctx, x, y, result, 32);
      else if(b == "rsb")
        asm_arm::set_sub_flags(ctx, y, x, result, 32);
      else if(b == "sbc")
      {
        // the flags of x + ~y + C
        asm_arm::set_add_flags(ctx, x, bitnot_exprt{y}, carry, result, 32);
      }
      else
      {
        // Logical operations and shifts: C is the carry out of the
        // shifter, which is not modeled (unchanged for a register operand
        // without shift); V is unchanged.
        asm_arm::set_nz(ctx, result, 32);
        if(
          ops[2].kind == a32_operandt::kindt::IMMEDIATE || b == "lsl" ||
          b == "lsr" || b == "asr" || b == "ror")
        {
          nondet_carry();
        }
      }
    }
    return write(ctx, ops[0], 32, result);
  }

  if(b == "cmp" || b == "cmn" || b == "tst" || b == "teq")
  {
    if(ops.size() != 2 || !is_reg(0) || !is_value(1))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    const symbol_exprt x = temp(read(ctx, ops[0], 32), "a");
    const symbol_exprt y = temp(read(ctx, ops[1], 32), "b");
    if(b == "cmp")
      asm_arm::set_sub_flags(ctx, x, y, temp(minus_exprt{x, y}, "r"), 32);
    else if(b == "cmn")
    {
      asm_arm::set_add_flags(
        ctx, x, y, constant(0, 32), temp(plus_exprt{x, y}, "r"), 32);
    }
    else
    {
      asm_arm::set_nz(
        ctx,
        temp(
          b == "tst" ? exprt{bitand_exprt{x, y}} : exprt{bitxor_exprt{x, y}},
          "r"),
        32);
      if(ops[1].kind == a32_operandt::kindt::IMMEDIATE)
        nondet_carry();
    }
    return true;
  }

  return lower_memory(decoded, ops, instruction, ctx);
}

bool asm_arm_semanticst::lower_memory(
  const a32_mnemonict &decoded,
  std::vector<a32_operandt> &ops,
  const asm_instructiont &instruction,
  asm_lowering_contextt &ctx) const
{
  const std::string &b = decoded.base;
  const bool conditional = decoded.condition != "al";

  auto is_reg = [&](std::size_t i)
  { return i < ops.size() && ops[i].kind == a32_operandt::kindt::REGISTER; };
  auto is_mem = [&](std::size_t i)
  { return i < ops.size() && ops[i].kind == a32_operandt::kindt::MEMORY; };

  static const std::map<std::string, std::pair<std::size_t, bool>> loads = {
    {"ldr", {32, false}},
    {"ldrb", {8, false}},
    {"ldrh", {16, false}},
    {"ldrsb", {8, true}},
    {"ldrsh", {16, true}},
    {"ldrex", {32, false}},
    {"ldrexb", {8, false}},
    {"ldrexh", {16, false}}};
  auto load = loads.find(b);
  if(load != loads.end())
  {
    if(ops.size() != 2 || !is_reg(0) || !is_mem(1))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    const std::size_t size = load->second.first;
    const exprt v = read(ctx, ops[1], size);
    if(!write(
         ctx,
         ops[0],
         32,
         load->second.second ? sign_extend(v, size, 32) : resize(v, 32)))
    {
      return false;
    }
    if(b.compare(0, 5, "ldrex") == 0)
      ctx.begin_exclusive();
    return true;
  }

  static const std::map<std::string, std::size_t> stores = {
    {"str", 32}, {"strb", 8}, {"strh", 16}};
  auto store = stores.find(b);
  if(store != stores.end())
  {
    if(ops.size() != 2 || !is_reg(0) || !is_mem(1))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    return write(ctx, ops[1], store->second, read(ctx, ops[0], store->second));
  }

  // store-exclusive: Rd, Rt, [Rn]
  static const std::map<std::string, std::size_t> exclusive_stores = {
    {"strex", 32}, {"strexb", 8}, {"strexh", 16}};
  auto xstore = exclusive_stores.find(b);
  if(xstore != exclusive_stores.end())
  {
    if(ops.size() != 3 || !is_reg(0) || !is_reg(1) || !is_mem(2))
      return ctx.fail("unsupported operands of " + instruction.mnemonic);
    const std::size_t size = xstore->second;
    if(ctx.exclusive_cleared())
    {
      // the store fails, and does not store
      return write(ctx, ops[0], 32, constant(1, 32));
    }
    // The store may fail spuriously; it can succeed without a load-exclusive
    // in this statement if the monitor was set before.
    if(ctx.exclusive_open())
      ctx.end_exclusive();
    const symbol_exprt success = ctx.temporary(bool_typet{}, "success");
    ctx.assign(success, ctx.nondet(bool_typet{}));
    const exprt value = read(ctx, ops[1], size);
    const auto skip = ctx.begin_conditional(success);
    if(!write(ctx, ops[2], size, value))
      return false;
    ctx.end_conditional(skip);
    // If the instruction is conditional, it may not execute, and the monitor
    // keeps its state.
    if(!conditional)
      ctx.clear_exclusive();
    if(!write(
         ctx, ops[0], 32, if_exprt{success, constant(0, 32), constant(1, 32)}))
    {
      return false;
    }
    // the status of a conditional store-exclusive may be unchanged
    if(!conditional)
      ctx.record_store_exclusive(success);
    return true;
  }

  return ctx.fail("unsupported instruction " + instruction.mnemonic);
}

bool asm_arm_semanticst::lower_system(
  const a32_mnemonict &decoded,
  std::vector<a32_operandt> &ops,
  asm_lowering_contextt &ctx) const
{
  const std::string &b = decoded.base;

  auto is_reg = [&](std::size_t i)
  { return i < ops.size() && ops[i].kind == a32_operandt::kindt::REGISTER; };
  auto is_name = [&](std::size_t i, const std::string &prefix)
  {
    return i < ops.size() && ops[i].kind == a32_operandt::kindt::NAME &&
           ops[i].name.compare(0, prefix.size(), prefix) == 0;
  };

  if(b == "mrs")
  {
    if(ops.size() != 2 || !is_reg(0) || !is_name(1, ""))
      return ctx.fail("unsupported mrs");
    const std::string &source = ops[1].name;
    if(source == "apsr" || source == "cpsr")
    {
      // N, Z, C, V are bits 31 to 28; the other bits are not modeled
      exprt value = bitand_exprt{ctx.nondet(bv(32)), constant(0x0fffffff, 32)};
      std::size_t bit = 31;
      for(const char *f : {"n", "z", "c", "v"})
      {
        value = bitor_exprt{
          value,
          shl_exprt{typecast_exprt{ctx.flag(f), bv(32)}, constant(bit--, 32)}};
      }
      return write(ctx, ops[0], 32, value);
    }
    // other special registers: their values are not modeled
    return write(ctx, ops[0], 32, ctx.nondet(bv(32)));
  }

  if(b == "msr")
  {
    if(ops.size() != 2 || !is_name(0, ""))
      return ctx.fail("unsupported msr");
    bool known, flags, control;
    msr_fields(ops[0].name, known, flags, control);
    if(!known)
      return ctx.fail("unsupported special register " + ops[0].name);
    if(
      ops[1].kind != a32_operandt::kindt::REGISTER &&
      ops[1].kind != a32_operandt::kindt::IMMEDIATE)
    {
      return ctx.fail("unsupported operands of msr");
    }
    if(flags)
    {
      const exprt value = read(ctx, ops[1], 32);
      const symbol_exprt v = ctx.temporary(value.type(), "psr");
      ctx.assign(v, value);
      std::size_t bit = 31;
      for(const char *f : {"n", "z", "c", "v"})
        ctx.assign(ctx.flag(f), extractbit_exprt{v, bit--});
    }
    // The other fields (the Q and GE flags, the interrupt masks, and the
    // processor mode) have no effect on the modeled state; see make_a32_state
    // for the registers that a change of mode affects.
    return true;
  }

  // mrc/mcr coproc, opc1, Rt, CRn, CRm[, opc2]
  if(
    ops.size() < 5 || ops.size() > 6 || !is_name(0, "p") || !is_reg(2) ||
    !is_name(3, "c") || !is_name(4, "c"))
  {
    return ctx.fail("unsupported operands of " + b);
  }

  if(b == "mrc")
  {
    // the value of a coprocessor register is not modeled
    return write(ctx, ops[2], 32, ctx.nondet(bv(32)));
  }

  // mcr: only CP15 operations without effect on the modeled state
  auto immediate = [&](std::size_t i) -> mp_integer
  {
    if(i >= ops.size())
      return 0;
    if(
      ops[i].kind != a32_operandt::kindt::IMMEDIATE ||
      ops[i].value.type().id() != ID_integer)
    {
      return -1;
    }
    return numeric_cast_v<mp_integer>(to_constant_expr(ops[i].value));
  };
  const std::string &crn = ops[3].name, &crm = ops[4].name;
  const mp_integer opc1 = immediate(1), opc2 = immediate(5);
  if(ops[0].name != "p15" || opc1 != 0)
    return ctx.fail("unsupported coprocessor operation");

  if(crn == "c7")
  {
    if(crm == "c10" && (opc2 == 4 || opc2 == 5))
    {
      // CP15DSB, CP15DMB
      ctx.fence(true, true, true, true, true);
      return true;
    }
    if(crm == "c5" && opc2 == 4)
    {
      // CP15ISB
      ctx.fence(false, false, false, false, false);
      return true;
    }
    // cache maintenance
    return true;
  }
  // TLB maintenance
  if(crn == "c8")
    return true;
  // the software thread ID registers
  if(crn == "c13" && crm == "c0" && opc2 >= 2 && opc2 <= 4)
    return true;

  return ctx.fail("unsupported coprocessor operation");
}

bool asm_arm_semanticst::parse_register_list(
  const asm_token_listt &tokens,
  asm_lowering_contextt &ctx,
  std::vector<a32_operandt> &registers,
  std::vector<std::string> &canonical) const
{
  std::vector<a32_list_entryt> entries;
  if(!register_list(tokens, entries))
    return ctx.fail("unsupported register list");
  // The registers are stored in the order of their numbers, which is not
  // known for operand references.
  if(entries.size() > 1)
  {
    for(const auto &entry : entries)
    {
      if(entry.number < 0)
        return ctx.fail("operand reference in a register list");
    }
  }
  std::stable_sort(
    entries.begin(),
    entries.end(),
    [](const a32_list_entryt &a, const a32_list_entryt &b)
    { return a.number < b.number; });
  for(std::size_t i = 0; i < entries.size(); ++i)
  {
    if(i > 0 && entries[i].number == entries[i - 1].number)
      return ctx.fail("register listed twice");
    // sp and pc (a load of which is a branch) are not modeled
    if(entries[i].number == 13)
      return ctx.fail("sp in a register list");
    a32_operandt reg;
    if(
      !parse_operand(entries[i].tokens, ctx, reg) ||
      reg.kind != a32_operandt::kindt::REGISTER)
    {
      return ctx.fail("unsupported register in a register list");
    }
    registers.push_back(reg);
    canonical.push_back(
      entries[i].number < 0 ? std::string{}
                            : "r" + std::to_string(entries[i].number));
  }
  return true;
}

bool asm_arm_semanticst::lower_multiple(
  const a32_multiplet &form,
  const asm_instructiont &instruction,
  const a32_statet &state,
  asm_lowering_contextt &ctx) const
{
  // Rn[!], {registers}
  if(form.push_pop || instruction.operands.size() != 2)
    return ctx.fail("unsupported operands of " + instruction.mnemonic);
  asm_token_listt base_tokens = instruction.operands[0];
  const bool writeback =
    !base_tokens.empty() && base_tokens.back().is_punctuation('!');
  if(writeback)
    base_tokens.pop_back();
  // In divided syntax for Thumb-1, ldmia and stmia without ! are assembled
  // with writeback (with a warning).
  else if(state.maybe_thumb1_divided)
    return ctx.fail("ldm or stm without writeback, which may be Thumb-1");
  a32_operandt base;
  if(
    !parse_operand(base_tokens, ctx, base) ||
    base.kind != a32_operandt::kindt::REGISTER)
  {
    return ctx.fail("unsupported base register");
  }

  std::vector<a32_operandt> registers;
  std::vector<std::string> canonical;
  if(!parse_register_list(instruction.operands[1], ctx, registers, canonical))
    return false;
  const std::size_t n = registers.size();
  bool base_listed = false;
  for(const auto &reg : registers)
    base_listed = base_listed || reg.storage == base.storage;
  // unpredictable, or (for stores) storing an unknown value
  if(writeback && base_listed)
    return ctx.fail("base register in the list with writeback");

  using modet = a32_multiplet::modet;
  const symbol_exprt address = ctx.temporary(bv(32), "base");
  ctx.assign(address, read(ctx, base, 32));
  long long first = 0;
  switch(form.mode)
  {
  case modet::INCREMENT_AFTER:
    first = 0;
    break;
  case modet::INCREMENT_BEFORE:
    first = 4;
    break;
  case modet::DECREMENT_AFTER:
    first = 4 - 4 * static_cast<long long>(n);
    break;
  case modet::DECREMENT_BEFORE:
    first = -4 * static_cast<long long>(n);
    break;
  }
  auto element = [&](std::size_t i)
  {
    a32_operandt memory;
    memory.kind = a32_operandt::kindt::MEMORY;
    memory.address = typecast_exprt{
      resize(
        plus_exprt{
          address, constant(first + 4 * static_cast<long long>(i), 32)},
        config.ansi_c.pointer_width),
      pointer_type(char_type())};
    return memory;
  };

  // all values are read before any register or memory is written
  std::vector<symbol_exprt> values;
  for(std::size_t i = 0; i < n; ++i)
  {
    const exprt value =
      form.load ? read(ctx, element(i), 32) : read(ctx, registers[i], 32);
    values.push_back(ctx.temporary(bv(32), "value"));
    ctx.assign(values.back(), value);
  }
  for(std::size_t i = 0; i < n; ++i)
  {
    if(!write(ctx, form.load ? registers[i] : element(i), 32, values[i]))
      return false;
  }
  if(writeback)
  {
    const long long delta = (form.mode == modet::INCREMENT_AFTER ||
                             form.mode == modet::INCREMENT_BEFORE)
                              ? 4 * static_cast<long long>(n)
                              : -4 * static_cast<long long>(n);
    return write(ctx, base, 32, plus_exprt{address, constant(delta, 32)});
  }
  return true;
}

bool asm_arm_semanticst::lower_stack(
  const a32_multiplet &form,
  const asm_instructiont &instruction,
  a32_statet &state,
  asm_lowering_contextt &ctx) const
{
  // The pushes and pops are balanced and in straight-line code
  // (make_a32_state), so that the stack memory they use is the statement's
  // own, below the stack pointer, where no C object is.
  if(ctx.exclusive_open())
    return ctx.fail("memory access between load-exclusive and store-exclusive");
  std::vector<a32_operandt> registers;
  std::vector<std::string> canonical;
  if(!parse_register_list(
       instruction.operands.back(), ctx, registers, canonical))
  {
    return false;
  }

  if(!form.load)
  {
    // the lowest register ends up at the lowest address, the top
    for(std::size_t i = registers.size(); i-- > 0;)
    {
      const symbol_exprt slot = ctx.temporary(bv(32), "stack");
      ctx.assign(slot, read(ctx, registers[i], 32));
      state.stack.push_back(slot);
    }
    return true;
  }

  if(registers.size() > state.stack.size())
    return ctx.fail("pop of registers that were not pushed");
  for(std::size_t i = 0; i < registers.size(); ++i)
  {
    const symbol_exprt slot = state.stack.back();
    state.stack.pop_back();
    if(!write(ctx, registers[i], 32, slot))
      return false;
  }
  return true;
}
} // namespace

std::unique_ptr<asm_semanticst> make_asm_arm_semantics()
{
  return std::make_unique<asm_arm_semanticst>();
}

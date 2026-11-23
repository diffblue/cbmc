/*******************************************************************\

Module: Inline assembly: the operand interface of GCC-style statements

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// The operand interface of GCC-style inline assembly statements

#include "asm_operands.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/string_constant.h>

#include "asm_semantics.h"

#include <cctype>

std::optional<std::size_t> asm_operandst::find(const irep_idt &name) const
{
  for(std::size_t i = 0; i < operands.size(); ++i)
  {
    if(!name.empty() && operands[i].name == name)
      return i;
  }
  return {};
}

std::optional<std::size_t> asm_operandst::find_label(const irep_idt &name) const
{
  for(std::size_t i = 0; i < label_names.size(); ++i)
  {
    if(label_names[i] == name)
      return i;
  }
  return {};
}

static std::string string_of(const exprt &expr)
{
  if(expr.id() == ID_string_constant)
    return id2string(to_string_constant(expr).value());
  return {};
}

/// Interpret \p constraint for operand \p operand
static bool parse_constraint(
  asm_operandt &operand,
  const asm_operandst &operands,
  const asm_semanticst *semantics,
  std::string &error)
{
  const std::string &constraint = operand.constraint;
  std::size_t pos = 0;

  // modifiers
  while(pos < constraint.size())
  {
    const char c = constraint[pos];
    if(c == '=')
      operand.is_read = false;
    else if(c == '+')
      operand.is_read = true;
    else if(c == '&' || c == '%' || c == '?' || c == '!' || c == '*')
    {
    }
    else
      break;
    ++pos;
  }

  if(constraint.compare(pos, 3, "@cc") == 0)
  {
    if(!operand.is_output)
    {
      error = "flag output constraint on input";
      return false;
    }
    operand.kind = asm_operandt::kindt::FLAG_OUTPUT;
    operand.flag_condition = constraint.substr(pos + 3);
    if(
      semantics == nullptr ||
      !semantics->is_flag_output_condition(operand.flag_condition))
    {
      error = "unsupported flag output constraint \"" + constraint + "\"";
      return false;
    }
    return true;
  }

  bool reg = false, mem = false, imm = false, any = false;
  std::string fixed;

  for(; pos < constraint.size(); ++pos)
  {
    const char c = constraint[pos];

    if(c == ',')
      break; // only the first alternative is used

    if(std::isdigit(static_cast<unsigned char>(c)))
    {
      std::size_t index = 0;
      while(pos < constraint.size() &&
            std::isdigit(static_cast<unsigned char>(constraint[pos])))
      {
        index = index * 10 + static_cast<std::size_t>(constraint[pos] - '0');
        ++pos;
      }
      --pos;
      if(operand.is_output || index >= operands.number_of_outputs)
      {
        error = "invalid matching constraint \"" + constraint + "\"";
        return false;
      }
      operand.tied_output = index;
      continue;
    }

    if(c == '[')
    {
      const auto end = constraint.find(']', pos);
      if(end == std::string::npos)
      {
        error = "malformed constraint \"" + constraint + "\"";
        return false;
      }
      const auto index =
        operands.find(constraint.substr(pos + 1, end - pos - 1));
      if(
        operand.is_output || !index.has_value() ||
        *index >= operands.number_of_outputs)
      {
        error = "invalid matching constraint \"" + constraint + "\"";
        return false;
      }
      operand.tied_output = *index;
      pos = end;
      continue;
    }

    switch(c)
    {
    case 'm':
    case 'o':
    case 'V':
    case '<':
    case '>':
      mem = true;
      continue;
    case 'r':
      reg = true;
      continue;
    case 'g':
    case 'X':
      any = true;
      continue;
    case 'i':
    case 'n':
    case 's':
    case 'E':
    case 'F':
      imm = true;
      continue;
    default:
      break;
    }

    asm_semanticst::constraint_classt cls =
      asm_semanticst::constraint_classt::UNKNOWN;
    std::string fixed_register;
    if(semantics != nullptr)
      cls = semantics->classify_constraint(constraint, pos, fixed_register);

    switch(cls)
    {
    case asm_semanticst::constraint_classt::REGISTER:
      reg = true;
      break;
    case asm_semanticst::constraint_classt::MEMORY:
      mem = true;
      break;
    case asm_semanticst::constraint_classt::IMMEDIATE:
      imm = true;
      break;
    case asm_semanticst::constraint_classt::ANY:
      any = true;
      break;
    case asm_semanticst::constraint_classt::FIXED_REGISTER:
      if(!fixed.empty() && fixed != fixed_register)
      {
        error = "constraint \"" + constraint + "\" names several registers";
        return false;
      }
      fixed = fixed_register;
      break;
    case asm_semanticst::constraint_classt::IGNORE:
      break;
    case asm_semanticst::constraint_classt::UNKNOWN:
      error = "unsupported constraint \"" + constraint + "\"";
      return false;
    }
  }

  if(operand.tied_output.has_value())
  {
    operand.kind = operands.operands[*operand.tied_output].kind;
    // an input tied to a memory output is that memory; GCC rejects anything
    // else
    if(
      operand.kind == asm_operandt::kindt::MEMORY &&
      operand.expr != operands.operands[*operand.tied_output].expr)
    {
      error = "input operand tied to a memory output is a different object";
      return false;
    }
    return true;
  }

  if(!fixed.empty())
  {
    operand.kind = asm_operandt::kindt::REGISTER;
    operand.fixed_register = fixed;
  }
  else if(reg || any)
  {
    // the compiler may choose a register whenever one is allowed; the effect
    // on the C value is the same either way
    operand.kind = asm_operandt::kindt::REGISTER;
  }
  else if(mem)
    operand.kind = asm_operandt::kindt::MEMORY;
  else if(imm && !operand.is_output)
    operand.kind = asm_operandt::kindt::IMMEDIATE;
  else
  {
    error = "unsupported constraint \"" + constraint + "\"";
    return false;
  }

  // as an rvalue in a register, an array decays to the address of its first
  // element, and a function to its address
  if(operand.kind == asm_operandt::kindt::REGISTER && !operand.is_output)
  {
    if(operand.expr.type().id() == ID_array)
    {
      operand.expr = address_of_exprt{
        index_exprt{operand.expr, from_integer(0, c_index_type())}};
    }
    else if(operand.expr.type().id() == ID_code)
      operand.expr = address_of_exprt{operand.expr};
  }

  if(
    operand.kind == asm_operandt::kindt::MEMORY && !operand.is_output &&
    !operand.expr.get_bool(ID_C_lvalue) && operand.expr.id() != ID_symbol &&
    operand.expr.id() != ID_dereference && operand.expr.id() != ID_index &&
    operand.expr.id() != ID_member)
  {
    error = "memory input operand is not an lvalue";
    return false;
  }

  return true;
}

bool asm_operandst::parse(
  const code_asm_gcct &code,
  const asm_semanticst *semantics,
  std::string &error)
{
  // basic asm has no colon at all: the four lists are not even nil
  is_basic = true;
  for(const exprt *list :
      {&code.outputs(), &code.inputs(), &code.clobbers(), &code.labels()})
  {
    if(!list->id().empty() || !list->operands().empty())
      is_basic = false;
  }

  for(const auto &output : code.outputs().operands())
  {
    if(output.id() != ID_gcc_asm_output || output.operands().size() != 2)
    {
      error = "malformed output operand";
      return false;
    }
    asm_operandt operand;
    operand.is_output = true;
    operand.constraint = string_of(to_binary_expr(output).op0());
    operand.expr = to_binary_expr(output).op1();
    operand.name = output.get(ID_identifier);
    operands.push_back(operand);
  }

  number_of_outputs = operands.size();

  for(const auto &input : code.inputs().operands())
  {
    if(input.id() != ID_gcc_asm_input || input.operands().size() != 2)
    {
      error = "malformed input operand";
      return false;
    }
    asm_operandt operand;
    operand.is_read = true;
    operand.constraint = string_of(to_binary_expr(input).op0());
    operand.expr = to_binary_expr(input).op1();
    operand.name = input.get(ID_identifier);
    operands.push_back(operand);
  }

  for(const auto &clobber : code.clobbers().operands())
  {
    std::string name = clobber.id() == ID_gcc_asm_clobbered_register
                         ? string_of(to_unary_expr(clobber).op())
                         : string_of(clobber);
    if(!name.empty() && name[0] == '%')
      name.erase(0, 1);
    clobbers.insert(name);
  }

  for(const auto &label : code.labels().operands())
  {
    labels.push_back(label.get(ID_identifier));
    const irep_idt &base_name = label.get(ID_C_base_name);
    label_names.push_back(
      base_name.empty() ? label.get(ID_identifier) : base_name);
  }

  for(auto &operand : operands)
  {
    if(!parse_constraint(operand, *this, semantics, error))
      return false;
  }

  return true;
}

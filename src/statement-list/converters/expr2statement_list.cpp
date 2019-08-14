/*******************************************************************\

Module: Conversion from Expression or Type to Statement List

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#include "expr2statement_list.h"

#include <ansi-c/expr2c.h>

#include <util/suffix.h>
#include <util/symbol_table.h>

#include <algorithm>
#include <cstring>
#include <iostream>

/// STL code for an AND instruction.
#define AND 'A'

/// STL code for an OR instruction.
#define OR 'O'

/// STL code for a XOR instruction.
#define XOR 'X'

/// Postfix for any negated boolean instruction.
#define NOT_POSTFIX 'N'

/// STL code for a NOT instruction.
#define NOT "NOT"

/// Separator between the instruction code and it's operand.
#define OPERAND_SEPARATOR ' '

/// Separator between the end of an instruction and the next one.
#define LINE_SEPARATOR ";\n"

/// Separator for the end of an instruction that introduces a new layer of
/// nesting.
#define NESTING_OPEN_LINE_SEPARATOR "(;\n"

/// Separator for the end of an instruction that closes a nesting layer. Also
/// known as the NESTING CLOSED instruction.
#define NESTING_CLOSED_LINE_SEPARATOR ");\n"

/// Prefix for the reference to any variable.
#define REFERENCE_FLAG '#'

/// CBMC-internal separator for variable scopes.
#define SCOPE_SEPARATOR "::"

/// Modifies the parameters of a binary equal expression with the help of its
/// symmetry properties. This function basically converts the operands to
/// operands of a XOR expression so that the whole expression can be treated as
/// such. This can reduce complexity in some cases.
/// \param lhs: Left side of the binary expression.
/// \param rhs: Right side of the binary expression.
/// \return: List of instrumented operands.
static std::vector<exprt>
instrument_equal_operands(const exprt &lhs, const exprt &rhs)
{
  std::vector<exprt> result;
  if(ID_not != lhs.id() && ID_not != rhs.id())
  {
    // lhs == rhs is equivalent to X lhs; XN rhs;
    result.push_back(lhs);
    result.push_back(not_exprt{rhs});
  }
  else if(ID_not != lhs.id() && ID_not == rhs.id())
  {
    // lhs == !rhs is equivalent to X lhs; X rhs;
    result.push_back(lhs);
    result.push_back(to_not_expr(rhs).op());
  }
  else if(ID_not == lhs.id() && ID_not != rhs.id())
  {
    // !lhs == rhs is equivalent to X lhs; X rhs;
    result.push_back(to_not_expr(lhs).op());
    result.push_back(rhs);
  }
  else // ID_not == lhs.id() && ID_not == rhs.id()
  {
    // !lhs == !rhs is equivalent to X lhs; XN rhs;
    result.push_back(to_not_expr(lhs).op());
    result.push_back(rhs);
  }
  return result;
}

/// Checks if the expression or one of its parameters is not of type bool.
/// \param expr: Expression to verify.
/// \return: True if the expression and its operands are not or only partially
///   of type bool, false otherwise.
static bool is_not_bool(const exprt &expr)
{
  if(!expr.is_boolean())
    return true;
  for(const exprt &op : expr.operands())
    if(!op.is_boolean())
      return true;
  return false;
}

std::string expr2stl(const exprt &expr, const namespacet &ns)
{
  expr2stlt expr2stl{ns};

  return expr2stl.convert(expr);
}

std::string type2stl(const typet &type, const namespacet &ns)
{
  // TODO: Implement type2stl.
  // Expand this section so that it is able to properly convert from
  // CBMC types to STL code.
  return type2c(type, ns);
}

expr2stlt::expr2stlt(const namespacet &ns)
  : inside_bit_string(false), is_reference(false), ns(ns)
{
}

std::string expr2stlt::convert(const exprt &expr)
{
  // Redirect to expr2c if no boolean expression.
  if(is_not_bool(expr))
    return expr2c(expr, ns);

  if(ID_and == expr.id())
    convert(to_and_expr(expr));
  else if(ID_or == expr.id())
    convert(to_or_expr(expr));
  else if(ID_xor == expr.id())
    convert(to_xor_expr(expr));
  else if(ID_notequal == expr.id())
    convert(to_notequal_expr(expr));
  else if(ID_equal == expr.id())
    convert(to_equal_expr(expr));
  else if(ID_symbol == expr.id())
    convert(to_symbol_expr(expr));
  else if(ID_not == expr.id() && to_not_expr(expr).op().type().id() == ID_bool)
    convert(to_not_expr(expr));
  else // TODO: support more instructions in expr2stl.
    return expr2c(expr, ns);

  return result.str();
}

void expr2stlt::convert(const and_exprt &expr)
{
  std::vector<exprt> operands = expr.operands();
  convert_multiary_bool(operands, AND);
}

void expr2stlt::convert(const or_exprt &expr)
{
  std::vector<exprt> operands = expr.operands();
  convert_multiary_bool(operands, OR);
}

void expr2stlt::convert(const xor_exprt &expr)
{
  std::vector<exprt> operands = expr.operands();
  convert_multiary_bool(operands, XOR);
}

void expr2stlt::convert(const notequal_exprt &expr)
{
  std::vector<exprt> operands = expr.operands();
  convert_multiary_bool(operands, XOR);
}

void expr2stlt::convert(const equal_exprt &expr)
{
  std::vector<exprt> operands =
    instrument_equal_operands(expr.lhs(), expr.rhs());
  convert_multiary_bool(operands, XOR);
}

void expr2stlt::convert(const not_exprt &expr)
{
  // If a NOT expression is being handled here it must always mark the
  // beginning of a new bit string.
  PRECONDITION(!inside_bit_string);

  if(ID_symbol == expr.op().id())
  {
    // Use AN to load the symbol.
    is_reference = true;
    result << AND << NOT_POSTFIX << OPERAND_SEPARATOR;
    convert(to_symbol_expr(expr.op()));
    result << LINE_SEPARATOR;
  }
  else
  {
    // Use NOT to negate the RLO after the wrapped expression was loaded.
    convert(expr.op());
    result << NOT LINE_SEPARATOR;
  }
}

void expr2stlt::convert(const symbol_exprt &expr)
{
  if(is_reference)
  {
    result << REFERENCE_FLAG;
    is_reference = false;
  }
  result << id2string(id_shorthand(expr.get_identifier()));
}

void expr2stlt::convert_multiary_bool(
  std::vector<exprt> &operands,
  const char operation)
{
  if(inside_bit_string)
    convert_multiary_bool_operands(operands, operation);
  else
  {
    convert_first_non_trivial_operand(operands);
    convert_multiary_bool_operands(operands, operation);
  }
}

void expr2stlt::convert_multiary_bool_operands(
  const std::vector<exprt> &operands,
  const char operation)
{
  for(const exprt &op : operands)
  {
    if(ID_not == op.id())
    {
      result << operation << NOT_POSTFIX;
      convert_bool_operand(to_not_expr(op).op());
    }
    else
    {
      result << operation;
      convert_bool_operand(op);
    }
  }
}

void expr2stlt::convert_bool_operand(const exprt &op)
{
  if(op.id() == ID_symbol)
  {
    is_reference = true;
    result << OPERAND_SEPARATOR;
    convert(to_symbol_expr(op));
    result << LINE_SEPARATOR;
  }
  else
  {
    inside_bit_string = false;
    result << NESTING_OPEN_LINE_SEPARATOR;
    convert(op);
    result << NESTING_CLOSED_LINE_SEPARATOR;
  }
}

void expr2stlt::convert_first_non_trivial_operand(std::vector<exprt> &operands)
{
  exprt non_trivial_op;
  for(auto it{begin(operands)}; it != end(operands); ++it)
  {
    if(
      (ID_symbol == it->id()) ||
      (ID_not == it->id() && ID_symbol == to_not_expr(*it).op().id()))
      continue;
    else
    {
      non_trivial_op = *it;
      operands.erase(it);
      break;
    }
  }
  // Important for some scenarios: Convert complex op first, set bit string
  // flag to true afterwards.
  if(non_trivial_op.is_not_nil())
    convert(non_trivial_op);

  inside_bit_string = true;
}

irep_idt expr2stlt::id_shorthand(const irep_idt &identifier)
{
  const symbolt *symbol;
  std::string shorthand = id2string(identifier);
  if(
    !ns.lookup(identifier, symbol) && !symbol->base_name.empty() &&
    has_suffix(shorthand, id2string(symbol->base_name)))
    return symbol->base_name;

  const std::string::size_type pos = shorthand.rfind(SCOPE_SEPARATOR);
  if(pos != std::string::npos)
    shorthand.erase(0, pos + std::strlen(SCOPE_SEPARATOR));

  return shorthand;
}

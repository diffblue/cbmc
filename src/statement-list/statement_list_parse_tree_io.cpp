/*******************************************************************\

Module: Statement List Language Parse Tree Output

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parse Tree Output

#include "statement_list_parse_tree_io.h"
#include "converters/statement_list_types.h"

#include <util/arith_tools.h>
#include <util/ieee_float.h>

/// String to indicate that there is no value.
#define NO_VALUE "(none)"

/// Prints a constant to the given output stream.
/// \param [out] os: Stream that should receive the result.
/// \param constant: Constant that shall be printed.
static void output_constant(std::ostream &os, const constant_exprt &constant)
{
  mp_integer ivalue;
  if(!to_integer(constant, ivalue))
    os << ivalue;
  else if(can_cast_type<floatbv_typet>(constant.type()))
  {
    ieee_floatt real{get_real_type()};
    real.from_expr(constant);
    os << real.to_float();
  }
  else
    os << constant.get_value();
}

/// Prints the assignment of a module parameter to the given output stream.
/// \param [out] os: Stream that should receive the result.
/// \param assignment: Assignment that shall be printed.
static void
output_parameter_assignment(std::ostream &os, const equal_exprt &assignment)
{
  os << assignment.lhs().get(ID_identifier) << " := ";
  const constant_exprt *const constant =
    expr_try_dynamic_cast<constant_exprt>(assignment.rhs());
  if(constant)
    output_constant(os, *constant);
  else
    os << assignment.rhs().get(ID_identifier);
}

void output_parse_tree(
  std::ostream &out,
  const statement_list_parse_treet &parse_tree)
{
  for(const auto &function_block : parse_tree.function_blocks)
  {
    out << "============== Function Block ==============\n";
    output_function_block(out, function_block);
    out << '\n';
  }

  for(const auto &function : parse_tree.functions)
  {
    out << "================= Function =================\n";
    output_function(out, function);
    out << '\n';
  }

  if(!parse_tree.tags.empty())
  {
    out << "================= Tag List =================\n";
    for(const auto &tag : parse_tree.tags)
    {
      out << tag.pretty();
      out << '\n';
    }
  }
}

void output_function_block(
  std::ostream &os,
  const statement_list_parse_treet::function_blockt &function_block)
{
  output_tia_module_properties(function_block, os);
  output_common_var_declarations(os, function_block);
  output_static_var_declarations(os, function_block);
  output_network_list(os, function_block.networks);
}

void output_function(
  std::ostream &os,
  const statement_list_parse_treet::functiont &function)
{
  output_tia_module_properties(function, os);
  output_return_value(function, os);
  output_common_var_declarations(os, function);
  output_network_list(os, function.networks);
}

void output_tia_module_properties(
  const statement_list_parse_treet::tia_modulet &module,
  std::ostream &os)
{
  os << "Name: " << module.name << '\n';
  os << "Version: " << module.version << "\n\n";
}

void output_return_value(
  const statement_list_parse_treet::functiont &function,
  std::ostream &os)
{
  os << "Return type: ";
  if(function.return_type.is_nil())
    os << "Void";
  else
    os << function.return_type.id();
  os << "\n\n";
}

void output_common_var_declarations(
  std::ostream &os,
  const statement_list_parse_treet::tia_modulet &module)
{
  if(!module.var_input.empty())
  {
    os << "--------- Input Variables ----------\n\n";
    output_var_declaration_list(os, module.var_input);
  }

  if(!module.var_inout.empty())
  {
    os << "--------- In/Out Variables ---------\n\n";
    output_var_declaration_list(os, module.var_inout);
  }

  if(!module.var_output.empty())
  {
    os << "--------- Output Variables ---------\n\n";
    output_var_declaration_list(os, module.var_output);
  }

  if(!module.var_constant.empty())
  {
    os << "-------- Constant Variables --------\n\n";
    output_var_declaration_list(os, module.var_constant);
  }

  if(!module.var_temp.empty())
  {
    os << "---------- Temp Variables ----------\n\n";
    output_var_declaration_list(os, module.var_temp);
  }
}

void output_static_var_declarations(
  std::ostream &os,
  const statement_list_parse_treet::function_blockt &block)
{
  if(!block.var_static.empty())
  {
    os << "--------- Static Variables ---------\n\n";
    output_var_declaration_list(os, block.var_static);
  }
}

void output_var_declaration_list(
  std::ostream &os,
  const statement_list_parse_treet::var_declarationst &declarations)
{
  for(const auto &declaration : declarations)
  {
    output_var_declaration(os, declaration);
    os << "\n\n";
  }
}

void output_var_declaration(
  std::ostream &os,
  const statement_list_parse_treet::var_declarationt &declaration)
{
  os << declaration.variable.pretty() << '\n';
  os << "  * default_value: ";
  if(declaration.default_value)
  {
    const constant_exprt &constant =
      to_constant_expr(declaration.default_value.value());
    output_constant(os, constant);
  }
  else
    os << NO_VALUE;
}

void output_network_list(
  std::ostream &os,
  const statement_list_parse_treet::networkst &networks)
{
  os << "-------------- Networks --------------\n\n";
  for(const auto &network : networks)
  {
    output_network(os, network);
    os << '\n';
  }
}

void output_network(
  std::ostream &os,
  const statement_list_parse_treet::networkt &network)
{
  os << "Title: " << network.title.value_or(NO_VALUE) << '\n';
  os << "Instructions: ";
  if(network.instructions.empty())
    os << NO_VALUE;
  os << '\n';
  for(const auto &instruction : network.instructions)
  {
    output_instruction(os, instruction);
    os << '\n';
  }
}

void output_instruction(
  std::ostream &os,
  const statement_list_parse_treet::instructiont &instruction)
{
  for(const codet &token : instruction.tokens)
  {
    os << token.get_statement();
    for(const auto &expr : token.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(expr);
      if(symbol)
      {
        os << '\t' << symbol->get_identifier();
        continue;
      }
      const constant_exprt *const constant =
        expr_try_dynamic_cast<constant_exprt>(expr);
      if(constant)
      {
        os << '\t';
        output_constant(os, *constant);
        continue;
      }
      const equal_exprt *const equal = expr_try_dynamic_cast<equal_exprt>(expr);
      if(equal)
      {
        os << "\n\t";
        output_parameter_assignment(os, *equal);
        continue;
      }
      os << '\t' << expr.id();
    }
  }
}

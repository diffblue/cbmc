/*******************************************************************\

Module: Statement List Language Parse Tree Output

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parse Tree Output

#include "statement_list_parse_tree_io.h"

#define NO_VALUE "(none)"

void output_parse_tree(
  std::ostream &out,
  const statement_list_parse_treet &parse_tree)
{
  for(const auto &function_block : parse_tree.function_blocks)
  {
    out << "============== Function Block ==============\n";
    output_function_block(out, function_block);
    out << "\n";
  }

  for(const auto &function : parse_tree.functions)
  {
    out << "================= Function =================\n";
    output_function(out, function);
    out << "\n";
  }
}

void output_function_block(
  std::ostream &out,
  const statement_list_parse_treet::function_blockt &function_block)
{
  output_tia_module_properties(function_block, out);
  output_common_var_declarations(out, function_block);
  output_static_var_declarations(out, function_block);
  output_network_list(out, function_block.networks);
}

void output_function(
  std::ostream &out,
  const statement_list_parse_treet::functiont &function)
{
  output_tia_module_properties(function, out);
  output_return_value(function, out);
  output_common_var_declarations(out, function);
  output_network_list(out, function.networks);
}

void output_tia_module_properties(
  const statement_list_parse_treet::tia_modulet &module,
  std::ostream &out)
{
  out << "Name: " << module.name << '\n';
  out << "Version: " << module.version << "\n\n";
}

void output_return_value(
  const statement_list_parse_treet::functiont &function,
  std::ostream &out)
{
  out << "Return type: ";
  if(function.return_type.is_nil())
    out << "Void";
  else
    out << function.return_type.id();
  out << "\n\n";
}

void output_common_var_declarations(
  std::ostream &out,
  const statement_list_parse_treet::tia_modulet &module)
{
  if(!module.var_input.empty())
  {
    out << "--------- Input Variables ----------\n\n";
    output_var_declaration_list(out, module.var_input);
  }

  if(!module.var_inout.empty())
  {
    out << "--------- In/Out Variables ---------\n\n";
    output_var_declaration_list(out, module.var_inout);
  }

  if(!module.var_output.empty())
  {
    out << "--------- Output Variables ---------\n\n";
    output_var_declaration_list(out, module.var_output);
  }

  if(!module.var_constant.empty())
  {
    out << "-------- Constant Variables --------\n\n";
    output_var_declaration_list(out, module.var_constant);
  }

  if(!module.var_temp.empty())
  {
    out << "---------- Temp Variables ----------\n\n";
    output_var_declaration_list(out, module.var_temp);
  }
}

void output_static_var_declarations(
  std::ostream &out,
  const statement_list_parse_treet::function_blockt &block)
{
  if(!block.var_static.empty())
  {
    out << "--------- Static Variables ---------\n\n";
    output_var_declaration_list(out, block.var_static);
  }
}

void output_var_declaration_list(
  std::ostream &out,
  const statement_list_parse_treet::var_declarationst &declarations)
{
  for(const auto &declaration : declarations)
  {
    output_var_declaration(out, declaration);
    out << "\n\n";
  }
}

void output_var_declaration(
  std::ostream &out,
  const statement_list_parse_treet::var_declarationt &declaration)
{
  out << declaration.variable.pretty() << "\n";
  out << "  * default_value: ";
  if(declaration.default_value)
    out << declaration.default_value->get(ID_value);
  else
    out << NO_VALUE;
}

void output_network_list(
  std::ostream &out,
  const statement_list_parse_treet::networkst &networks)
{
  out << "-------------- Networks --------------\n\n";
  for(const auto &network : networks)
  {
    output_network(out, network);
    out << "\n";
  }
}

void output_network(
  std::ostream &out,
  const statement_list_parse_treet::networkt &network)
{
  out << "Title: " << network.title.value_or(NO_VALUE) << "\n";
  out << "Instructions: ";
  if(network.instructions.empty())
    out << NO_VALUE;
  out << "\n";
  for(const auto &instruction : network.instructions)
  {
    output_instruction(out, instruction);
    out << "\n";
  }
}

void output_instruction(
  std::ostream &out,
  const statement_list_parse_treet::instructiont &instruction)
{
  for(const codet &token : instruction.tokens)
  {
    out << token.get_statement();
    for(const auto &expr : token.operands())
    {
      if(expr.id() == ID_symbol)
        out << "\t" << expr.get(ID_identifier);
      else if(expr.id() == ID_constant)
        out << "\t" << expr.get(ID_value);
      else if(can_cast_expr<equal_exprt>(expr))
      {
        const equal_exprt eq = to_equal_expr(expr);
        out << "\n\t" << eq.lhs().get(ID_identifier)
            << " := " << eq.rhs().get(ID_identifier);
      }
      else
        out << "\t" << expr.id();
    }
  }
}

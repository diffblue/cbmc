/*******************************************************************\

Module: Statement List Language Parser

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parser

#include "statement_list_parser.h"

#include "statement_list_parse_tree.h"
#include <cmath>
#include <iostream>
#include <util/expr.h>

statement_list_parsert statement_list_parser;

extern char *yystatement_listtext;

int yystatement_listerror(const std::string &error)
{
  statement_list_parser.parse_error(error, yystatement_listtext);
  return 0;
}

void statement_list_parsert::add_function_block(exprt &block)
{
  INVARIANT(
    block.id() == ID_statement_list_function_block,
    "Root expression ID should be ID_statement_list_function_block");

  // Generate new function block.
  statement_list_parse_treet::function_blockt fb{find_name(block),
                                                 find_version(block)};

  // Fill the block with networks and variables.
  exprt var_list = find_variable_list(block);
  find_variables(fb, var_list);
  exprt network_list = find_network_list(block);
  find_networks(fb, network_list);

  parse_tree.add_function_block(fb);
}

void statement_list_parsert::add_function(exprt &function)
{
  INVARIANT(
    function.id() == ID_statement_list_function,
    "Expression ID should be statement_list_function");

  // Generate new function.
  statement_list_parse_treet::functiont fn{find_name(function),
                                           find_version(function)};

  // Fill the function with networks and variables.
  exprt var_decls = find_variable_list(function);
  find_variables(fn, var_decls);
  exprt network_list = find_network_list(function);
  find_networks(fn, network_list);

  parse_tree.add_function(fn);
}

void statement_list_parsert::clear()
{
  parsert::clear();
  parse_tree.clear();
}

void statement_list_parsert::print_tree(std::ostream &out) const
{
  parse_tree.output(out);
}

irep_idt statement_list_parsert::find_name(const exprt &root)
{
  for(exprt op : root.operands())
  {
    if(op.get(ID_statement_list_type) == ID_statement_list_identifier)
      return op.get(ID_value);
  }

  UNREACHABLE; // Root expression should always have a name
}

float statement_list_parsert::find_version(const exprt &root)
{
  for(exprt op : root.operands())
  {
    if(op.type().id() == ID_statement_list_version)
      return std::stof(op.get(ID_value).c_str());
  }

  UNREACHABLE; // Root expression should always have a version
}

exprt statement_list_parsert::find_variable_list(const exprt &root)
{
  for(exprt op : root.operands())
  {
    if(op.id() == ID_statement_list_var_decls)
      return op;
  }
  UNREACHABLE; // Root expression should always have a variable list
}

exprt statement_list_parsert::find_network_list(const exprt &root)
{
  for(exprt op : root.operands())
  {
    if(op.id() == ID_statement_list_networks)
      return op;
  }

  UNREACHABLE; // Root expression should always have a network list
}

void statement_list_parsert::find_variables(
  statement_list_parse_treet::functiont &function,
  const exprt &var_decls)
{
  for(exprt decls : var_decls.operands())
  {
    if(decls.id() == ID_statement_list_var_input)
      fill_input_vars(function, decls);
    else if(decls.id() == ID_statement_list_var_inout)
      fill_output_vars(function, decls);
    else if(decls.id() == ID_statement_list_var_output)
      fill_output_vars(function, decls);
  }
}

void statement_list_parsert::fill_input_vars(
  statement_list_parse_treet::functiont &function,
  const exprt &input_vars)
{
  for(exprt entry : input_vars.operands())
  {
    irep_idt identifier;
    typet type;
    for(exprt part : entry.operands())
    {
      if(part.get(ID_statement_list_type) == ID_statement_list_identifier)
        identifier = part.get(ID_value);
      else
        type = typet(part.id());
    }

    statement_list_parse_treet::var_declarationt declaration(identifier, type);
    function.add_var_input_entry(declaration);
  }
}

void statement_list_parsert::fill_inout_vars(
  statement_list_parse_treet::functiont &function,
  const exprt &inout_vars)
{
  for(exprt entry : inout_vars.operands())
  {
    irep_idt identifier;
    typet type;
    for(exprt part : entry.operands())
    {
      if(part.get(ID_statement_list_type) == ID_statement_list_identifier)
        identifier = part.get(ID_value);
      else
        type = typet(part.id());
    }

    statement_list_parse_treet::var_declarationt declaration(identifier, type);
    function.add_var_inout_entry(declaration);
  }
}

void statement_list_parsert::fill_output_vars(
  statement_list_parse_treet::functiont &function,
  const exprt &output_vars)
{
  for(exprt entry : output_vars.operands())
  {
    irep_idt identifier;
    typet type;
    for(exprt part : entry.operands())
    {
      if(part.get(ID_statement_list_type) == ID_statement_list_identifier)
        identifier = part.get(ID_value);
      else
        type = typet(part.id());
    }

    statement_list_parse_treet::var_declarationt declaration(identifier, type);
    function.add_var_output_entry(declaration);
  }
}

void statement_list_parsert::find_networks(
  statement_list_parse_treet::functiont &function,
  const exprt &network_list)
{
  for(exprt expr_network : network_list.operands())
  {
    std::string title(find_network_title(expr_network));
    statement_list_parse_treet::networkt network(title);
    exprt instructions = find_network_instructions(expr_network);
    find_instructions(network, instructions);
    function.add_network(network);
  }
}

std::string statement_list_parsert::find_network_title(const exprt &network)
{
  for(exprt network_element : network.operands())
  {
    if(network_element.get(ID_statement_list_type) == ID_statement_list_title)
      return network_element.get(ID_value).c_str();
  }
  UNREACHABLE; // Network expression should always have a title
}

exprt statement_list_parsert::find_network_instructions(const exprt &network)
{
  for(exprt network_element : network.operands())
  {
    if(network_element.id() == ID_statement_list_instructions)
      return network_element;
  }
  UNREACHABLE; // Network expression should always have an instruction list
}

void statement_list_parsert::find_instructions(
  statement_list_parse_treet::networkt &network,
  const exprt &instructions)
{
  for(exprt expr_instruction : instructions.operands())
  {
    statement_list_parse_treet::instructiont instruction;
    codet code_token(expr_instruction.op0().id());
    for(exprt expr : expr_instruction.operands())
    {
      if(expr.id() != ID_nil && expr.id() != code_token.get_statement())
        code_token.add_to_operands(expr);
    }
    instruction.add_token(code_token);
    network.add_instruction(instruction);
  }
}

void statement_list_parsert::swap_tree(statement_list_parse_treet &other)
{
  parse_tree.swap(other);
}

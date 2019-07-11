/*******************************************************************\

Module: Statement List Language Parser

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parser

#include "statement_list_parser.h"

#include "converters/statement_list_types.h"
#include "statement_list_parse_tree.h"
#include "statement_list_parse_tree_io.h"
#include <algorithm>
#include <cmath>
#include <iostream>
#include <iterator>
#include <util/string_constant.h>

statement_list_parsert statement_list_parser;

extern char *yystatement_listtext;

/// Searches for the name of the TIA module inside of its root
/// expression.
/// \param root: Expression that includes the element's name as a
///   direct operand.
/// \return The name of the function element.
static irep_idt find_name(const exprt &root)
{
  for(const exprt &op : root.operands())
  {
    if(op.get(ID_statement_list_type) == ID_statement_list_identifier)
      return op.get(ID_value);
  }
  UNREACHABLE; // Root expression should always have a name
}

void statement_list_parsert::add_tag_list(const exprt &tag_list)
{
  const exprt::operandst &ops = tag_list.operands();
  transform(
    begin(ops),
    end(ops),
    std::back_inserter(parse_tree.tags),
    static_cast<const symbol_exprt &(*)(const exprt &)>(to_symbol_expr));
}

/// Searches for the version of the TIA module inside of its root
/// expression.
/// \param root: Expression that includes the element's version as a
///   direct operand.
/// \return The version of the element.
static std::string find_version(const exprt &root)
{
  for(const exprt &op : root.operands())
  {
    if(op.get(ID_statement_list_type) == ID_statement_list_version)
    {
      const string_constantt &constant{to_string_constant(op)};
      return id2string(constant.get_value());
    }
  }
  UNREACHABLE; // Root expression should always have a version
}

/// Searches for the return type of a function inside of its root
/// expression.
/// \param root: Expression that includes the function's return type as a
///   direct operand.
/// \return The return type of the function.
static typet find_return_value(const exprt &root)
{
  INVARIANT(
    root.id() == ID_statement_list_function,
    "Expression ID should be statement_list_function");

  for(const exprt &op : root.operands())
  {
    if(op.get(ID_statement_list_type) == ID_statement_list_return)
      return op.type();
  }

  UNREACHABLE; // Root expression of FC should always have a return value
}

/// Searches for the variable list of the TIA module inside of its root
/// expression.
/// \param root: Expression that includes the element's variable list as a
///   direct operand.
/// \return The variable list of the element.
static exprt find_variable_list(const exprt &root)
{
  for(const exprt &op : root.operands())
  {
    if(op.id() == ID_statement_list_var_decls)
      return op;
  }
  UNREACHABLE; // Root expression should always have a variable list
}

/// Adds all variable declarations (which can have a default value) to the
/// given list.
/// \param parse_tree_list: The list to fill with all declarations.
/// \param var_list: The root expression of a variable list with optional
///   default values.
static void fill_vars_with_default_values(
  statement_list_parse_treet::var_declarationst &parse_tree_list,
  const exprt &var_list)
{
  for(const exprt &entry : var_list.operands())
  {
    std::vector<symbol_exprt> symbols;
    exprt default_value = nil_exprt();
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
        symbols.push_back(*symbol);
      else
        default_value = part;
    }

    for(const symbol_exprt &symbol : symbols)
    {
      statement_list_parse_treet::var_declarationt declaration{symbol};
      if(default_value.is_not_nil())
        declaration.default_value = default_value;
      parse_tree_list.push_back(declaration);
    }
  }
}

/// Adds all temp variable declarations (variable declarations which can't have
/// a default value) to the given list.
/// \param parse_tree_list: The list to fill with all declarations.
/// \param temp_vars: The root expression of a temp variable list.
static void fill_temp_vars(
  statement_list_parse_treet::var_declarationst &parse_tree_list,
  const exprt &temp_vars)
{
  for(const exprt &entry : temp_vars.operands())
  {
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
      {
        statement_list_parse_treet::var_declarationt declaration{*symbol};
        parse_tree_list.push_back(declaration);
      }
      else
        UNREACHABLE; // Temp variables should not have an initial value.
    }
  }
}

/// Adds all valid variable declarations to the given function.
/// \param function: The TIA element to which the variables belong.
/// \param var_decls: The root expression of a valid variable list.
static void find_variables(
  statement_list_parse_treet::functiont &function,
  const exprt &var_decls)
{
  for(const exprt &decls : var_decls.operands())
  {
    if(decls.id() == ID_statement_list_var_input)
      fill_vars_with_default_values(function.var_input, decls);
    else if(decls.id() == ID_statement_list_var_inout)
      fill_vars_with_default_values(function.var_inout, decls);
    else if(decls.id() == ID_statement_list_var_output)
      fill_vars_with_default_values(function.var_output, decls);
    else if(decls.id() == ID_statement_list_var_constant)
      fill_vars_with_default_values(function.var_constant, decls);
    else if(decls.id() == ID_statement_list_var_temp)
      fill_temp_vars(function.var_temp, decls);
  }
}

/// Adds all valid variable declarations to the given function block.
/// \param block: The TIA element to which the variables belong.
/// \param var_decls: The root expression of a valid variable list.
static void find_variables(
  statement_list_parse_treet::function_blockt &block,
  const exprt &var_decls)
{
  for(const exprt &decls : var_decls.operands())
  {
    if(ID_statement_list_var_input == decls.id())
      fill_vars_with_default_values(block.var_input, decls);
    else if(ID_statement_list_var_inout == decls.id())
      fill_vars_with_default_values(block.var_inout, decls);
    else if(ID_statement_list_var_output == decls.id())
      fill_vars_with_default_values(block.var_output, decls);
    else if(ID_statement_list_var_static == decls.id())
      fill_vars_with_default_values(block.var_static, decls);
    else if(ID_statement_list_var_constant == decls.id())
      fill_vars_with_default_values(block.var_constant, decls);
    else if(ID_statement_list_var_temp == decls.id())
      fill_temp_vars(block.var_temp, decls);
  }
}

/// Searches for the network list of the TIA element inside of its root
/// expression.
/// \param root: Expression that includes the element's network list as a
///   direct operand.
/// \return The network list of the element.
static exprt find_network_list(const exprt &root)
{
  for(const exprt &op : root.operands())
  {
    if(op.id() == ID_statement_list_networks)
      return op;
  }
  UNREACHABLE; // Root expression should always have a network list
}

/// Searches for the title of a network inside of its root expression.
/// \param network: Expression that includes the network's title as a
///   direct operand.
/// \return The title of the network.
static std::string find_network_title(const exprt &network)
{
  for(const exprt &network_element : network.operands())
  {
    if(network_element.get(ID_statement_list_type) == ID_statement_list_title)
      return network_element.get(ID_value).c_str();
  }
  UNREACHABLE; // Network expression should always have a title
}

/// Searches for the instruction list of a network inside of its root
/// expression.
/// \param network: Expression that includes the network's instructions as a
///   direct operand.
/// \return The instruction list expression of the network.
static exprt find_network_instructions(const exprt &network)
{
  for(const exprt &network_element : network.operands())
  {
    if(network_element.id() == ID_statement_list_instructions)
      return network_element;
  }
  UNREACHABLE; // Network expression should always have an instruction list
}

/// Adds all valid  instructions to the given network.
/// \param network: The network to which the instructions belong.
/// \param instructions: The root expression of a valid instruction list.
static void find_instructions(
  statement_list_parse_treet::networkt &network,
  const exprt &instructions)
{
  for(const exprt &instruction_expr : instructions.operands())
  {
    statement_list_parse_treet::instructiont instruction;
    codet code_token(instruction_expr.op0().id());
    for(const exprt &operand : instruction_expr.operands())
    {
      if(operand.is_not_nil() && operand.id() != code_token.get_statement())
        code_token.add_to_operands(operand);
    }
    instruction.add_token(code_token);
    network.add_instruction(instruction);
  }
}

/// Adds all valid networks and their instructions to the given function
/// element.
/// \param module: The TIA element to which the networks belong.
/// \param network_list: The root expression of a valid network list.
static void find_networks(
  statement_list_parse_treet::tia_modulet &module,
  const exprt &network_list)
{
  for(const exprt &expr_network : network_list.operands())
  {
    const std::string title(find_network_title(expr_network));
    statement_list_parse_treet::networkt network(title);
    const exprt instructions = find_network_instructions(expr_network);
    find_instructions(network, instructions);
    module.add_network(network);
  }
}

void statement_list_parsert::add_function_block(const exprt &block)
{
  INVARIANT(
    block.id() == ID_statement_list_function_block,
    "Root expression ID should be ID_statement_list_function_block");

  // Generate new function block.
  statement_list_parse_treet::function_blockt fb{find_name(block),
                                                 find_version(block)};

  // Fill the block with networks and variables.
  find_variables(fb, find_variable_list(block));
  find_networks(fb, find_network_list(block));

  parse_tree.add_function_block(fb);
}

void statement_list_parsert::add_function(const exprt &function)
{
  INVARIANT(
    function.id() == ID_statement_list_function,
    "Expression ID should be statement_list_function");

  // Generate new function.
  statement_list_parse_treet::functiont fn{
    find_name(function), find_version(function), find_return_value(function)};

  // Fill the function with networks and variables.
  find_variables(fn, find_variable_list(function));
  find_networks(fn, find_network_list(function));

  parse_tree.add_function(fn);
}

bool statement_list_parsert::parse()
{
  return yystatement_listparse() != 0;
}

int yystatement_listerror(const std::string &error)
{
  statement_list_parser.parse_error(error, yystatement_listtext);
  return 0;
}

void statement_list_parsert::clear()
{
  parsert::clear();
  parse_tree.clear();
}

void statement_list_parsert::print_tree(std::ostream &out) const
{
  output_parse_tree(out, parse_tree);
}

void statement_list_parsert::swap_tree(statement_list_parse_treet &other)
{
  parse_tree.swap(other);
}

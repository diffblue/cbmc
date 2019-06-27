/*******************************************************************\

Module: Statement List Language Parser

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parser

#include "statement_list_parser.h"

#include "statement_list_parse_tree.h"
#include "statement_list_parse_tree_io.h"
#include <cmath>
#include <iostream>
#include <util/expr.h>

statement_list_parsert statement_list_parser;

extern char *yystatement_listtext;

bool statement_list_parsert::parse()
{
  return yystatement_listparse() != 0;
}

int yystatement_listerror(const std::string &error)
{
  statement_list_parser.parse_error(error, yystatement_listtext);
  return 0;
}

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

/// Searches for the version of the TIA module inside of its root
/// expression.
/// \param root: Expression that includes the element's version as a
///   direct operand.
/// \return The version of the element.
static std::string find_version(const exprt &root)
{
  for(const exprt &op : root.operands())
  {
    if(op.type().id() == ID_statement_list_version)
      return id2string(op.get(ID_value));
  }
  UNREACHABLE; // Root expression should always have a version
}

/// Searches for the return type of a function inside of its root
/// expression.
/// \param root: Expression that includes the function's return type as a
///   direct operand.
/// \return The return value of the function.
static typet find_return_value(const exprt &root)
{
  INVARIANT(
    root.id() == ID_statement_list_function,
    "Expression ID should be statement_list_function");

  for(const exprt &op : root.operands())
  {
    if(op.get(ID_statement_list_type) == ID_statement_list_return)
      return typet(op.id());
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

/// Adds all input variable declarations to the given element.
/// \param module: The TIA element to which the variables belong.
/// \param input_vars: The root expression of a input variable list.
static void fill_input_vars(
  statement_list_parse_treet::tia_modulet &module,
  const exprt &input_vars)
{
  for(const exprt &entry : input_vars.operands())
  {
    std::vector<irep_idt> identifiers;
    typet type;
    exprt default_value = nil_exprt();
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
        identifiers.push_back(symbol->get_identifier());
      else if(part.get(ID_statement_list_type) == ID_statement_list_type_name)
        type = typet(part.id());
      else
        default_value = part;
    }

    for(const irep_idt &identifier : identifiers)
    {
      statement_list_parse_treet::var_declarationt declaration{identifier,
                                                               type};
      if(default_value.is_not_nil())
        declaration.default_value = default_value;
      module.add_var_input_entry(declaration);
    }
  }
}

/// Adds all inout variable declarations to the given module.
/// \param module: The TIA element to which the variables belong.
/// \param inout_vars: The root expression of a inout variable list.
static void fill_inout_vars(
  statement_list_parse_treet::tia_modulet &module,
  const exprt &inout_vars)
{
  for(const exprt &entry : inout_vars.operands())
  {
    std::vector<irep_idt> identifiers;
    typet type;
    exprt default_value = nil_exprt();
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
        identifiers.push_back(symbol->get_identifier());
      else if(part.get(ID_statement_list_type) == ID_statement_list_type_name)
        type = typet(part.id());
      else
        default_value = part;
    }

    for(const irep_idt &identifier : identifiers)
    {
      statement_list_parse_treet::var_declarationt declaration{identifier,
                                                               type};
      if(default_value.is_not_nil())
        declaration.default_value = default_value;
      module.add_var_inout_entry(declaration);
    }
  }
}

/// Adds all output variable declarations to the given module.
/// \param module: The TIA element to which the variables belong.
/// \param output_vars: The root expression of a output variable list.
static void fill_output_vars(
  statement_list_parse_treet::tia_modulet &module,
  const exprt &output_vars)
{
  for(const exprt &entry : output_vars.operands())
  {
    std::vector<irep_idt> identifiers;
    typet type;
    exprt default_value = nil_exprt();
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
        identifiers.push_back(symbol->get_identifier());
      else if(part.get(ID_statement_list_type) == ID_statement_list_type_name)
        type = typet(part.id());
      else
        default_value = part;
    }

    for(const irep_idt &identifier : identifiers)
    {
      statement_list_parse_treet::var_declarationt declaration{identifier,
                                                               type};
      if(default_value.is_not_nil())
        declaration.default_value = default_value;
      module.add_var_output_entry(declaration);
    }
  }
}

/// Adds all temp variable declarations to the given module.
/// \param module: The TIA element to which the variables belong.
/// \param temp_vars: The root expression of a temp variable list.
static void fill_temp_vars(
  statement_list_parse_treet::tia_modulet &module,
  const exprt &temp_vars)
{
  for(const exprt &entry : temp_vars.operands())
  {
    std::vector<irep_idt> identifiers;
    typet type;
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
        identifiers.push_back(symbol->get_identifier());
      else if(part.get(ID_statement_list_type) == ID_statement_list_type_name)
        type = typet(part.id());
      else
        UNREACHABLE; // Temp vars should have no initial value.
    }

    for(const irep_idt &identifier : identifiers)
    {
      statement_list_parse_treet::var_declarationt declaration{identifier,
                                                               type};
      module.add_var_temp_entry(declaration);
    }
  }
}

/// Adds all constant variable declarations to the given module.
/// \param module: The TIA element to which the variables belong.
/// \param constant_vars: The root expression of a constant variable list.
static void fill_constant_vars(
  statement_list_parse_treet::tia_modulet &module,
  const exprt &constant_vars)
{
  for(const exprt &entry : constant_vars.operands())
  {
    std::vector<irep_idt> identifiers;
    typet type;
    exprt default_value = nil_exprt();
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
        identifiers.push_back(symbol->get_identifier());
      else if(part.get(ID_statement_list_type) == ID_statement_list_type_name)
        type = typet(part.id());
      else
        default_value = part;
    }

    for(const irep_idt &identifier : identifiers)
    {
      statement_list_parse_treet::var_declarationt declaration{identifier,
                                                               type};
      if(!default_value.is_nil())
        declaration.default_value = default_value;
      module.add_var_constant_entry(declaration);
    }
  }
}

/// Adds all static variable declarations to the given function block.
/// \param block: The TIA element to which the variables belong.
/// \param static_vars: The root expression of a static variable list.
static void fill_static_vars(
  statement_list_parse_treet::function_blockt &block,
  const exprt &static_vars)
{
  for(const exprt &entry : static_vars.operands())
  {
    std::vector<irep_idt> identifiers;
    typet type;
    exprt default_value = nil_exprt();
    for(const exprt &part : entry.operands())
    {
      const symbol_exprt *const symbol =
        expr_try_dynamic_cast<symbol_exprt>(part);
      if(symbol)
        identifiers.push_back(symbol->get_identifier());
      else if(part.get(ID_statement_list_type) == ID_statement_list_type_name)
        type = typet(part.id());
      else
        default_value = part;
    }

    for(const irep_idt &identifier : identifiers)
    {
      statement_list_parse_treet::var_declarationt declaration{identifier,
                                                               type};
      if(default_value.is_not_nil())
        declaration.default_value = default_value;
      block.add_var_static_entry(declaration);
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
      fill_input_vars(function, decls);
    else if(decls.id() == ID_statement_list_var_inout)
      fill_inout_vars(function, decls);
    else if(decls.id() == ID_statement_list_var_output)
      fill_output_vars(function, decls);
    else if(decls.id() == ID_statement_list_var_constant)
      fill_constant_vars(function, decls);
    else if(decls.id() == ID_statement_list_var_temp)
      fill_temp_vars(function, decls);
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
    if(decls.id() == ID_statement_list_var_input)
      fill_input_vars(block, decls);
    else if(decls.id() == ID_statement_list_var_inout)
      fill_inout_vars(block, decls);
    else if(decls.id() == ID_statement_list_var_output)
      fill_output_vars(block, decls);
    else if(decls.id() == ID_statement_list_var_static)
      fill_static_vars(block, decls);
    else if(decls.id() == ID_statement_list_var_constant)
      fill_constant_vars(block, decls);
    else if(decls.id() == ID_statement_list_var_temp)
      fill_temp_vars(block, decls);
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
    std::string title(find_network_title(expr_network));
    statement_list_parse_treet::networkt network(title);
    exprt instructions = find_network_instructions(expr_network);
    find_instructions(network, instructions);
    module.add_network(network);
  }
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
  statement_list_parse_treet::functiont fn{
    find_name(function), find_version(function), find_return_value(function)};

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
  output_parse_tree(out, parse_tree);
}

void statement_list_parsert::swap_tree(statement_list_parse_treet &other)
{
  parse_tree.swap(other);
}

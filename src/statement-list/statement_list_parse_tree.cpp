/*******************************************************************\

Module: Statement List Language Parse Tree

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parse Tree

#include "statement_list_parse_tree.h"

void statement_list_parse_treet::tia_modulet::add_var_input_entry(
  const var_declarationt &declaration)
{
  var_input.push_back(declaration);
}

void statement_list_parse_treet::tia_modulet::add_var_inout_entry(
  const var_declarationt &declaration)
{
  var_inout.push_back(declaration);
}

void statement_list_parse_treet::tia_modulet::add_var_output_entry(
  const var_declarationt &declaration)
{
  var_output.push_back(declaration);
}

void statement_list_parse_treet::tia_modulet::add_var_constant_entry(
  const var_declarationt &declaration)
{
  var_constant.push_back(declaration);
}

void statement_list_parse_treet::tia_modulet::add_var_temp_entry(
  const var_declarationt &declaration)
{
  var_temp.push_back(declaration);
}

void statement_list_parse_treet::function_blockt::add_var_static_entry(
  const var_declarationt &declaration)
{
  var_static.push_back(declaration);
}

void statement_list_parse_treet::tia_modulet::add_network(networkt &network)
{
  networks.push_back(network);
}

void statement_list_parse_treet::networkt::set_title(const std::string &value)
{
  if(value.empty())
    title.reset();
  else
    title = value;
}

statement_list_parse_treet::networkt::networkt(const std::string &title)
{
  set_title(title);
}

void statement_list_parse_treet::networkt::add_instruction(
  const instructiont &inst)
{
  instructions.push_back(inst);
}

statement_list_parse_treet::tia_modulet::tia_modulet(
  const irep_idt &name,
  const std::string &version)
  : name(name), version(version)
{
}

statement_list_parse_treet::function_blockt::function_blockt(
  const irep_idt &name,
  const std::string &version)
  : tia_modulet(name, version)
{
}

void statement_list_parse_treet::add_function_block(function_blockt &block)
{
  function_blocks.push_back(std::move(block));
}

void statement_list_parse_treet::add_function(functiont &function)
{
  functions.push_back(std::move(function));
}

void statement_list_parse_treet::clear()
{
  function_blocks.clear();
  functions.clear();
  tags.clear();
}

void statement_list_parse_treet::swap(statement_list_parse_treet &other)
{
  function_blocks.swap(other.function_blocks);
  functions.swap(other.functions);
  tags.swap(other.tags);
}

statement_list_parse_treet::functiont::functiont(
  const irep_idt &name,
  const std::string &version,
  const typet &return_type)
  : tia_modulet(name, version), return_type(return_type)
{
}

void statement_list_parse_treet::instructiont::add_token(const codet &token)
{
  tokens.push_back(token);
}

statement_list_parse_treet::var_declarationt::var_declarationt(
  const symbol_exprt &symbol)
  : variable(symbol)
{
}

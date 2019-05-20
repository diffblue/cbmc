/*******************************************************************\

Module: Statement List Language Parse Tree

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parse Tree

#include "statement_list_parse_tree.h"

void statement_list_parse_treet::output(std::ostream &out) const
{
  for(const auto &function_block : function_blocks)
  {
    out << "============== Function Block ==============\n";
    function_block.output(out);
    out << "\n";
  }

  for(const auto &function : functions)
  {
    out << "================= Function =================\n";
    function.output(out);
    out << "\n";
  }
}

void statement_list_parse_treet::functiont::output(std::ostream &out) const
{
  out << "Name: " << name << "\n";
  out << "Version: " << version << "\n\n";

  out << "--------- Input Variables ----------\n\n";
  for(const auto &declaration : var_input)
  {
    declaration.output(out);
    out << "\n\n";
  }

  out << "--------- In/Out Variables ---------\n\n";
  for(const auto &declaration : var_inout)
  {
    declaration.output(out);
    out << "\n\n";
  }

  out << "--------- Output Variables ---------\n\n";
  for(const auto &declaration : var_output)
  {
    declaration.output(out);
    out << "\n\n";
  }

  out << "------------- Networks -------------\n\n";
  for(const auto &network : networks)
  {
    network.output(out);
    out << "\n";
  }
}

void statement_list_parse_treet::function_blockt::output(
  std::ostream &out) const
{
  statement_list_parse_treet::functiont::output(out);
}

void statement_list_parse_treet::var_declarationt::output(
  std::ostream &out) const
{
  out << variable.pretty() << "\n";
  out << "  * initial_value: (default)";
}

void statement_list_parse_treet::networkt::output(std::ostream &out) const
{
  out << "Title: " << title.value_or("(none)") << "\n";
  out << "Instructions: ";
  if(instructions.empty())
    out << "(none)";
  out << "\n";
  for(const auto &instruction : instructions)
  {
    instruction.output(out);
    out << "\n";
  }
}

void statement_list_parse_treet::instructiont::output(std::ostream &out) const
{
  for(const auto &token : tokens)
  {
    out << token.get_statement();
    for(const auto expr : token.operands())
    {
      if(expr.id() == ID_symbol)
        out << "\t" << expr.get(ID_identifier);
      else if(expr.id() == ID_constant)
        out << "\t" << expr.get(ID_value);
      else
        out << "\t" << expr.id();
    }
  }
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
}

void statement_list_parse_treet::swap(statement_list_parse_treet &other)
{
  function_blocks.swap(other.function_blocks);
  functions.swap(other.functions);
}

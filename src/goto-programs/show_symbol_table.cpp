/*******************************************************************\

Module: Show the symbol table

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show the symbol table

#include "show_symbol_table.h"

#include <iostream>
#include <memory>

#include <langapi/language.h>
#include <langapi/mode.h>

#include "goto_model.h"

void show_symbol_table_xml_ui(formattert &)
{
}

void show_symbol_table_brief_plain(
  const symbol_tablet &symbol_table,
  std::ostream &out,
  formattert &formatter)
{
  // we want to sort alphabetically
  std::set<std::string> symbols;

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    symbols.insert(id2string(symbol_pair.first));
  }

  const namespacet ns(symbol_table);

  for(const std::string &id : symbols)
  {
    const symbolt &symbol=ns.lookup(id);

    if(symbol.type.is_not_nil())
      out << symbol.name << " " << formatter(symbol.type) << '\n';
    else
      out << symbol.name << '\n';
  }
}

void show_symbol_table_plain(
  const symbol_tablet &symbol_table,
  std::ostream &out,
  formattert &formatter)
{
  out << '\n' << "Symbols:" << '\n' << '\n';

  // we want to sort alphabetically
  std::set<std::string> symbols;

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    symbols.insert(id2string(symbol_pair.first));
  }

  const namespacet ns(symbol_table);

  for(const std::string &id : symbols)
  {
    const symbolt &symbol=ns.lookup(id);

    std::string type_str, value_str;

    out << "Symbol......: " << symbol.name << '\n' << std::flush;
    out << "Pretty name.: " << symbol.pretty_name << '\n';
    out << "Module......: " << symbol.module << '\n';
    out << "Base name...: " << symbol.base_name << '\n';
    out << "Mode........: " << symbol.mode << '\n';

    out << "Type........: ";
    if(symbol.type.is_not_nil())
      out << formatter(symbol.type);
    out << '\n';

    out << "Value.......: ";
    if(symbol.value.is_not_nil())
      out << formatter(symbol.value);
    out << '\n';

    out << "Flags.......:";

    if(symbol.is_lvalue)
      out << " lvalue";
    if(symbol.is_static_lifetime)
      out << " static_lifetime";
    if(symbol.is_thread_local)
      out << " thread_local";
    if(symbol.is_file_local)
      out << " file_local";
    if(symbol.is_type)
      out << " type";
    if(symbol.is_extern)
      out << " extern";
    if(symbol.is_input)
      out << " input";
    if(symbol.is_output)
      out << " output";
    if(symbol.is_macro)
      out << " macro";
    if(symbol.is_parameter)
      out << " parameter";
    if(symbol.is_auxiliary)
      out << " auxiliary";
    if(symbol.is_weak)
      out << " weak";
    if(symbol.is_property)
      out << " property";
    if(symbol.is_state_var)
      out << " state_var";
    if(symbol.is_exported)
      out << " exported";
    if(symbol.is_volatile)
      out << " volatile";

    out << '\n';
    out << "Location....: " << formatter(symbol.location) << '\n';

    out << '\n' << std::flush;
  }
}

void show_symbol_table(
  const symbol_tablet &symbol_table,
  ui_message_handlert::uit ui,
  formattert &formatter)
{
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_plain(symbol_table, std::cout, formatter);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui(formatter);
    break;

  default:
    break;
  }
}

void show_symbol_table(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui,
  formattert &formatter)
{
  show_symbol_table(goto_model.symbol_table, ui, formatter);
}

void show_symbol_table_brief(
  const symbol_tablet &symbol_table,
  ui_message_handlert::uit ui,
  formattert &formatter)
{
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_brief_plain(symbol_table, std::cout, formatter);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui(formatter);
    break;

  default:
    break;
  }
}

void show_symbol_table_brief(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui,
  formattert &formatter)
{
  show_symbol_table_brief(goto_model.symbol_table, ui, formatter);
}

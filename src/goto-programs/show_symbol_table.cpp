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
#include <util/cmdline.h>
#include <util/exit_codes.h>
#include <util/string_utils.h>

#include "goto_model.h"

symbol_table_filtert::symbol_table_filtert()
  : filter_lvalue(false),
    filter_static_lifetime(false),
    filter_thread_local(false),
    filter_file_local(false),
    filter_type(false),
    filter_extern(false),
    filter_input(false),
    filter_output(false),
    filter_macro(false),
    filter_parameter(false),
    filter_auxilary(false),
    filter_weak(false),
    filter_property(false),
    filter_state_var(false),
    filter_exported(false),
    filter_volatile(false),
    default_pass(true)
{
}

bool symbol_table_filtert::set_filter_flag(
  const std::string &flag)
{
  if(flag == "lvalue")
    filter_lvalue = true;
  else if(flag == "static_lifetime")
    filter_static_lifetime = true;
  else if(flag == "thread_local")
    filter_thread_local = true;
  else if(flag == "file_local")
    filter_file_local = true;
  else if(flag == "type")
    filter_type = true;
  else if(flag == "extern")
    filter_extern = true;
  else if(flag == "input")
    filter_input = true;
  else if(flag == "output")
    filter_output = true;
  else if(flag == "macro")
    filter_macro = true;
  else if(flag == "parameter")
    filter_parameter = true;
  else if(flag == "auxiliary")
    filter_auxilary = true;
  else if(flag == "weak")
    filter_weak = true;
  else if(flag == "property")
    filter_property = true;
  else if(flag == "state_var")
    filter_state_var = true;
  else if(flag == "exported")
    filter_exported = true;
  else if(flag == "volatile")
    filter_volatile = true;
  else
  {
    std::cout << "Don't recognize the following flag: " + flag + "\n\n"
              << "Only the following flags are valid:\n"
              << "  lvalue, static_lifetime, thread_local, file_local,\n"
              << "  type, extern, input, output, macro, parameter,\n"
              << "  auxiliary, weak, property, state_var, exported, volatile\n";
    return true;
  }
  return false;
}

bool symbol_table_filtert::is_selected(const symbolt &symbol) const
{
  return default_pass ||
         ((symbol.is_lvalue && filter_lvalue) ||
          (symbol.is_static_lifetime && filter_static_lifetime) ||
          (symbol.is_thread_local && filter_thread_local) ||
          (symbol.is_file_local && filter_file_local) ||
          (symbol.is_type && filter_type) ||
          (symbol.is_extern && filter_extern) ||
          (symbol.is_input && filter_input) ||
          (symbol.is_output && filter_output) ||
          (symbol.is_macro && filter_macro) ||
          (symbol.is_parameter && filter_parameter) ||
          (symbol.is_auxiliary && filter_auxilary) ||
          (symbol.is_weak && filter_weak) ||
          (symbol.is_property && filter_property) ||
          (symbol.is_state_var && filter_state_var) ||
          (symbol.is_exported && filter_exported) ||
          (symbol.is_volatile && filter_volatile));
}

bool symbol_table_filtert::setup(const std::string &flags)
{
  default_pass = false;
  std::vector<std::string> flags_splitted;
  split_string(flags, ',', flags_splitted, true, true);
  for(auto const &flag : flags_splitted)
  {
    if(set_filter_flag(flag))
    {
      return true;
    }
  }
  return false;
}

bool check_commandline_for_show_symbol_flags(
  int &return_value,
  const cmdlinet &cmdline,
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  if(cmdline.isset("show-symbol-table"))
  {
    if(cmdline.isset("filter-symbol-table"))
    {
      symbol_table_filtert filter;
      if(filter.setup(cmdline.get_value("filter-symbol-table")))
      {
        return_value = CPROVER_EXIT_USAGE_ERROR;
        return false;
      }

      show_symbol_table(goto_model, filter, ui);
      return_value = CPROVER_EXIT_SUCCESS;
      return false;
    }
    show_symbol_table(goto_model, ui);
    return_value = CPROVER_EXIT_SUCCESS;
    return false;
  }
  if(cmdline.isset("list-symbols") || cmdline.isset("list-symbol-table"))
  {
    if(cmdline.isset("filter-symbol-table"))
    {
      symbol_table_filtert filter;
      if(filter.setup(cmdline.get_value("filter-symbol-table")))
      {
        return_value = CPROVER_EXIT_USAGE_ERROR;
        return false;
      }

      show_symbol_table_brief(goto_model, filter, ui);
      return_value = CPROVER_EXIT_SUCCESS;
      return false;
    }
    show_symbol_table_brief(goto_model, ui);
    return_value = CPROVER_EXIT_SUCCESS;
    return false;
  }
  return true;
}

void show_symbol_table_xml_ui()
{
}

void show_symbol_table_brief_plain(
  const symbol_tablet &symbol_table,
  const symbol_table_filtert &filter,
  std::ostream &out)
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

    std::unique_ptr<languaget> ptr;

    if(symbol.mode=="")
      ptr=get_default_language();
    else
    {
      ptr=get_language_from_mode(symbol.mode);
      if(ptr==nullptr)
        throw "symbol "+id2string(symbol.name)+" has unknown mode";
    }

    std::string type_str;

    if(symbol.type.is_not_nil())
      ptr->from_type(symbol.type, type_str, ns);

    if(filter.is_selected(symbol))
      out << symbol.name << " " << type_str << '\n';
  }
}

void show_symbol_table_plain(
  const symbol_tablet &symbol_table,
  const symbol_table_filtert &filter,
  std::ostream &out)
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

    std::unique_ptr<languaget> ptr;

    if(symbol.mode=="")
    {
      ptr=get_default_language();
    }
    else
    {
      ptr=get_language_from_mode(symbol.mode);
    }

    if(!ptr)
      throw "symbol "+id2string(symbol.name)+" has unknown mode";

    std::string type_str, value_str;

    if(symbol.type.is_not_nil())
      ptr->from_type(symbol.type, type_str, ns);

    if(symbol.value.is_not_nil())
      ptr->from_expr(symbol.value, value_str, ns);

    if(!filter.is_selected(symbol))
    {
      continue;
    }
    out << "Symbol......: " << symbol.name << '\n' << std::flush;
    out << "Pretty name.: " << symbol.pretty_name << '\n';
    out << "Module......: " << symbol.module << '\n';
    out << "Base name...: " << symbol.base_name << '\n';
    out << "Mode........: " << symbol.mode << '\n';
    out << "Type........: " << type_str << '\n';
    out << "Value.......: " << value_str << '\n';
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
    out << "Location....: " << symbol.location << '\n';

    out << '\n' << std::flush;
  }
}

void show_symbol_table(
  const symbol_tablet &symbol_table,
  ui_message_handlert::uit ui)
{
  symbol_table_filtert filter;
  show_symbol_table(symbol_table, filter, ui);
}

void show_symbol_table(
  const symbol_tablet &symbol_table,
  const symbol_table_filtert &filter,
  ui_message_handlert::uit ui)
{
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_plain(symbol_table, filter, std::cout);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui();
    break;

  default:
    break;
  }
}

void show_symbol_table(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  show_symbol_table(goto_model.symbol_table, ui);
}

void show_symbol_table(
  const goto_modelt &goto_model,
  const symbol_table_filtert &filter,
  ui_message_handlert::uit ui)
{
  show_symbol_table(goto_model.symbol_table, filter, ui);
}

void show_symbol_table_brief(
  const symbol_tablet &symbol_table,
  ui_message_handlert::uit ui)
{
  symbol_table_filtert filter;
  show_symbol_table_brief(symbol_table, filter, ui);
}

void show_symbol_table_brief(
  const symbol_tablet &symbol_table,
  const symbol_table_filtert &filter,
  ui_message_handlert::uit ui)
{
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_brief_plain(symbol_table, filter, std::cout);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui();
    break;

  default:
    break;
  }
}

void show_symbol_table_brief(
  const goto_modelt &goto_model,
  const symbol_table_filtert &filter,
  ui_message_handlert::uit ui)
{
  show_symbol_table_brief(goto_model.symbol_table, filter, ui);
}

void show_symbol_table_brief(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  show_symbol_table_brief(goto_model.symbol_table, ui);
}

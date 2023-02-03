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

#include <util/json_irep.h>
#include <util/json_stream.h>
#include <util/ui_message.h>

#include "goto_model.h"

/// \brief Gets the language which should be used for showing the type and value
///   of the supplied \p symbol.
/// \return A unique pointer, pointing to the language corresponding to the mode
///   of the \p symbol in the case where the symbol specifies a known/registered
///   language mode. Returns the globally configured default language/first
///   language registered in the case where mode is empty or does not correspond
///   to a known registered language. The enables showing the symbol even if the
///   language is not recognised.
static std::unique_ptr<languaget>
get_show_symbol_language(const symbolt &symbol)
{
  if(!symbol.mode.empty())
    if(auto language_from_mode = get_language_from_mode(symbol.mode))
      return language_from_mode;
  return get_default_language();
}

void show_symbol_table_xml_ui()
{
}

void show_symbol_table_brief_plain(
  const symbol_table_baset &symbol_table,
  std::ostream &out)
{
  // we want to sort alphabetically
  const namespacet ns(symbol_table);

  for(const auto &id : symbol_table.sorted_symbol_names())
  {
    const symbolt &symbol=ns.lookup(id);

    const std::unique_ptr<languaget> ptr = get_show_symbol_language(symbol);

    std::string type_str;

    if(symbol.type.is_not_nil())
      ptr->from_type(symbol.type, type_str, ns);

    out << symbol.name << " " << type_str << '\n';
  }
}

void show_symbol_table_plain(
  const symbol_table_baset &symbol_table,
  std::ostream &out)
{
  out << '\n' << "Symbols:" << '\n' << '\n';

  const namespacet ns(symbol_table);

  // we want to sort alphabetically
  for(const irep_idt &id : symbol_table.sorted_symbol_names())
  {
    const symbolt &symbol=ns.lookup(id);

    const std::unique_ptr<languaget> ptr = get_show_symbol_language(symbol);

    std::string type_str, value_str;

    if(symbol.type.is_not_nil())
      ptr->from_type(symbol.type, type_str, ns);

    if(symbol.value.is_not_nil())
      ptr->from_expr(symbol.value, value_str, ns);

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

static void show_symbol_table_json_ui(
  const symbol_table_baset &symbol_table,
  ui_message_handlert &message_handler)
{
  json_stream_arrayt &out = message_handler.get_json_stream();

  json_stream_objectt &result_wrapper = out.push_back_stream_object();
  json_stream_objectt &result =
    result_wrapper.push_back_stream_object("symbolTable");

  const namespacet ns(symbol_table);
  json_irept irep_converter(true);

  for(const auto &id_and_symbol : symbol_table.symbols)
  {
    const symbolt &symbol = id_and_symbol.second;

    const std::unique_ptr<languaget> ptr = get_show_symbol_language(symbol);

    std::string type_str, value_str;

    if(symbol.type.is_not_nil())
      ptr->from_type(symbol.type, type_str, ns);

    if(symbol.value.is_not_nil())
      ptr->from_expr(symbol.value, value_str, ns);

    json_objectt symbol_json{
      {"prettyName", json_stringt(symbol.pretty_name)},
      {"name", json_stringt(symbol.name)},
      {"baseName", json_stringt(symbol.base_name)},
      {"mode", json_stringt(symbol.mode)},
      {"module", json_stringt(symbol.module)},

      {"prettyType", json_stringt(type_str)},
      {"prettyValue", json_stringt(value_str)},

      {"type", irep_converter.convert_from_irep(symbol.type)},
      {"value", irep_converter.convert_from_irep(symbol.value)},
      {"location", irep_converter.convert_from_irep(symbol.location)},

      {"isType", jsont::json_boolean(symbol.is_type)},
      {"isMacro", jsont::json_boolean(symbol.is_macro)},
      {"isExported", jsont::json_boolean(symbol.is_exported)},
      {"isInput", jsont::json_boolean(symbol.is_input)},
      {"isOutput", jsont::json_boolean(symbol.is_output)},
      {"isStateVar", jsont::json_boolean(symbol.is_state_var)},
      {"isProperty", jsont::json_boolean(symbol.is_property)},
      {"isStaticLifetime", jsont::json_boolean(symbol.is_static_lifetime)},
      {"isThreadLocal", jsont::json_boolean(symbol.is_thread_local)},
      {"isLvalue", jsont::json_boolean(symbol.is_lvalue)},
      {"isFileLocal", jsont::json_boolean(symbol.is_file_local)},
      {"isExtern", jsont::json_boolean(symbol.is_extern)},
      {"isVolatile", jsont::json_boolean(symbol.is_volatile)},
      {"isParameter", jsont::json_boolean(symbol.is_parameter)},
      {"isAuxiliary", jsont::json_boolean(symbol.is_auxiliary)},
      {"isWeak", jsont::json_boolean(symbol.is_weak)}};

    result.push_back(id2string(symbol.name), std::move(symbol_json));
  }
}

static void show_symbol_table_brief_json_ui(
  const symbol_table_baset &symbol_table,
  ui_message_handlert &message_handler)
{
  json_stream_arrayt &out = message_handler.get_json_stream();

  json_stream_objectt &result_wrapper = out.push_back_stream_object();
  json_stream_objectt &result =
    result_wrapper.push_back_stream_object("symbolTable");

  const namespacet ns(symbol_table);
  json_irept irep_converter(true);

  for(const auto &id_and_symbol : symbol_table.symbols)
  {
    const symbolt &symbol = id_and_symbol.second;

    const std::unique_ptr<languaget> ptr = get_show_symbol_language(symbol);

    std::string type_str, value_str;

    if(symbol.type.is_not_nil())
      ptr->from_type(symbol.type, type_str, ns);

    json_objectt symbol_json{
      {"prettyName", json_stringt(symbol.pretty_name)},
      {"baseName", json_stringt(symbol.base_name)},
      {"mode", json_stringt(symbol.mode)},
      {"module", json_stringt(symbol.module)},

      {"prettyType", json_stringt(type_str)},

      {"type", irep_converter.convert_from_irep(symbol.type)}};

    result.push_back(id2string(symbol.name), std::move(symbol_json));
  }
}

void show_symbol_table(
  const symbol_table_baset &symbol_table,
  ui_message_handlert &ui)
{
  switch(ui.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_plain(symbol_table, std::cout);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui();
    break;

  case ui_message_handlert::uit::JSON_UI:
    show_symbol_table_json_ui(symbol_table, ui);
    break;
  }
}

void show_symbol_table(
  const goto_modelt &goto_model,
  ui_message_handlert &ui)
{
  show_symbol_table(goto_model.symbol_table, ui);
}

void show_symbol_table_brief(
  const symbol_table_baset &symbol_table,
  ui_message_handlert &ui)
{
  switch(ui.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_brief_plain(symbol_table, std::cout);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui();
    break;

  case ui_message_handlert::uit::JSON_UI:
    show_symbol_table_brief_json_ui(symbol_table, ui);
    break;
  }
}

void show_symbol_table_brief(
  const goto_modelt &goto_model,
  ui_message_handlert &ui)
{
  show_symbol_table_brief(goto_model.symbol_table, ui);
}

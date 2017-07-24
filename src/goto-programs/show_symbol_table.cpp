/*******************************************************************\

Module: Show the symbol table

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show the symbol table

#include "show_symbol_table.h"

#include <iostream>
#include <memory>

#include <util/language.h>
#include <langapi/mode.h>

#include "goto_model.h"

void show_symbol_table_xml_ui()
{
}

void show_symbol_table_plain(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  out << '\n' << "Symbols:" << '\n' << '\n';

  // we want to sort alphabetically
  std::set<std::string> symbols;

  forall_symbols(it, goto_model.symbol_table.symbols)
    symbols.insert(id2string(it->first));

  const namespacet ns(goto_model.symbol_table);

  for(const std::string &id : symbols)
  {
    const symbolt &symbol=ns.lookup(id);

    languaget *ptr;

    if(symbol.mode=="")
      ptr=get_default_language();
    else
    {
      ptr=get_language_from_mode(symbol.mode);
      if(ptr==NULL)
        throw "symbol "+id2string(symbol.name)+" has unknown mode";
    }

    std::unique_ptr<languaget> p(ptr);
    std::string type_str, value_str;

    if(symbol.type.is_not_nil())
      p->from_type(symbol.type, type_str, ns);

    if(symbol.value.is_not_nil())
      p->from_expr(symbol.value, value_str, ns);

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
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_plain(goto_model, std::cout);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui();
    break;

  default:
    break;
  }
}

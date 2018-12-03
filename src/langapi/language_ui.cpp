/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "language_ui.h"

#include <fstream>
#include <memory>
#include <iostream>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/options.h>
#include <util/unicode.h>

#include "language.h"
#include "mode.h"

/// Constructor
language_uit::language_uit(
  const cmdlinet &cmdline,
  ui_message_handlert &_ui_message_handler,
  optionst *_options)
  : _cmdline(cmdline),
    ui_message_handler(_ui_message_handler),
    options(_options)
{
  set_message_handler(ui_message_handler);
}

/// Destructor
language_uit::~language_uit()
{
}

bool language_uit::parse()
{
  for(const auto &filename : _cmdline.args)
    if(parse(filename))
      return true;

  return false;
}

bool language_uit::parse(const std::string &filename)
{
  #ifdef _MSC_VER
  std::ifstream infile(widen(filename));
  #else
  std::ifstream infile(filename);
  #endif

  if(!infile)
  {
    error() << "failed to open input file `" << filename << "'" << eom;
    return true;
  }

  language_filet &lf=language_files.add_file(filename);
  lf.language=get_language_from_filename(filename);

  if(lf.language==nullptr)
  {
    source_locationt location;
    location.set_file(filename);
    error().source_location=location;
    error() << "failed to figure out type of file" << eom;
    return true;
  }

  languaget &language=*lf.language;
  language.set_message_handler(get_message_handler());

  if(options != nullptr)
    language.set_language_options(*options);

  status() << "Parsing " << filename << eom;

  if(language.parse(infile, filename))
  {
    if(get_ui()==ui_message_handlert::uit::PLAIN)
      std::cerr << "PARSING ERROR\n";

    return true;
  }

  lf.get_modules();

  return false;
}

bool language_uit::typecheck()
{
  status() << "Converting" << eom;

  language_files.set_message_handler(*message_handler);

  if(language_files.typecheck(symbol_table))
  {
    error() << "CONVERSION ERROR" << eom;
    return true;
  }

  return false;
}

bool language_uit::final()
{
  language_files.set_message_handler(*message_handler);

  // TODO: This should be moved elsewhere because it is not used in
  //       this repository.
  // Enable/disable stub generation for opaque methods
  bool stubs_enabled = false;
  if(options != nullptr)
    stubs_enabled = options->is_set("generate-opaque-stubs");
  language_files.set_should_generate_opaque_method_stubs(stubs_enabled);

  if(language_files.final(symbol_table))
  {
    error() << "CONVERSION ERROR" << eom;
    return true;
  }

  config.set_object_bits_from_symbol_table(symbol_table);

  return false;
}

void language_uit::show_symbol_table(bool brief)
{
  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    show_symbol_table_plain(std::cout, brief);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_symbol_table_xml_ui(brief);
    break;

  default:
    error() << "cannot show symbol table in this format" << eom;
  }
}

void language_uit::show_symbol_table_xml_ui(bool)
{
  error() << "cannot show symbol table in this format" << eom;
}

void language_uit::show_symbol_table_plain(
  std::ostream &out,
  bool brief)
{
  if(!brief)
    out << "\nSymbols:\n\n";

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

    if(brief)
    {
      out << symbol.name << " " << type_str << '\n';
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

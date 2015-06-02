/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <fstream>
#include <memory>
#include <iostream>

#include <util/i2string.h>
#include <util/namespace.h>
#include <util/language.h>
#include <util/cmdline.h>
#include <util/unicode.h>

#include "language_ui.h"
#include "mode.h"

/*******************************************************************\

Function: get_ui_cmdline

  Inputs:

 Outputs:

 Purpose: Constructor

\*******************************************************************/

static ui_message_handlert::uit get_ui_cmdline(const cmdlinet &cmdline)
{
  if(cmdline.isset("xml-ui"))
    return ui_message_handlert::XML_UI;

  return ui_message_handlert::PLAIN;
}

/*******************************************************************\

Function: language_uit::language_uit

  Inputs:

 Outputs:

 Purpose: Constructor

\*******************************************************************/

language_uit::language_uit(
  const std::string &program,
  const cmdlinet &__cmdline):
  ui_message_handler(get_ui_cmdline(__cmdline), program),
  _cmdline(__cmdline)
{
  set_message_handler(ui_message_handler);
}
   
/*******************************************************************\

Function: language_uit::~language_uit

  Inputs:

 Outputs:

 Purpose: Destructor

\*******************************************************************/

language_uit::~language_uit()
{
}

/*******************************************************************\

Function: language_uit::parse()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_uit::parse()
{
  for(unsigned i=0; i<_cmdline.args.size(); i++)
  {
    if(parse(_cmdline.args[i]))
      return true;
  }
   
  return false;
}

/*******************************************************************\

Function: language_uit::parse()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_uit::parse(const std::string &filename)
{
  #ifdef _MSC_VER
  std::ifstream infile(widen(filename).c_str());
  #else
  std::ifstream infile(filename.c_str());
  #endif

  if(!infile)
  {
    error() << "failed to open input file `" << filename << "'" << eom;
    return true;
  }

  std::pair<language_filest::filemapt::iterator, bool>
    result=language_files.filemap.insert(
      std::pair<std::string, language_filet>(filename, language_filet()));

  language_filet &lf=result.first->second;

  lf.filename=filename;
  lf.language=get_language_from_filename(filename);

  if(lf.language==NULL)
  {
    error("failed to figure out type of file", filename);
    return true;
  }
  
  languaget &language=*lf.language;
  language.set_message_handler(get_message_handler());

  status() << "Parsing " << filename << eom;

  if(language.parse(infile, filename))
  {
    if(get_ui()==ui_message_handlert::PLAIN)
      std::cerr << "PARSING ERROR" << std::endl;

    return true;
  }

  lf.get_modules();
   
  return false;
}

/*******************************************************************\

Function: language_uit::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_uit::typecheck()
{
  status() << "Converting" << eom;
  
  language_files.set_message_handler(*message_handler);

  if(language_files.typecheck(symbol_table))
  {
    if(get_ui()==ui_message_handlert::PLAIN)
      std::cerr << "CONVERSION ERROR" << std::endl;
      
    return true;
  }

  return false;
}
 
/*******************************************************************\

Function: language_uit::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_uit::final()
{
  language_files.set_message_handler(*message_handler);

  if(language_files.final(symbol_table))
  {
    if(get_ui()==ui_message_handlert::PLAIN)
      std::cerr << "CONVERSION ERROR" << std::endl;

    return true;
  }

  return false;
}

/*******************************************************************\

Function: language_uit::show_symbol_table

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void language_uit::show_symbol_table(bool brief)
{
  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    show_symbol_table_plain(std::cout, brief);
    break;

  case ui_message_handlert::XML_UI:
    show_symbol_table_xml_ui(brief);
    break;

  default:
    error() << "cannot show symbol table in this format" << eom;
  }
}

/*******************************************************************\

Function: language_uit::show_symbol_table_xml_ui

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void language_uit::show_symbol_table_xml_ui(bool brief)
{
  error() << "cannot show symbol table in this format" << eom;
}

/*******************************************************************\

Function: language_uit::show_symbol_table_plain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void language_uit::show_symbol_table_plain(std::ostream &out, bool brief)
{
  if(!brief)
    out << std::endl << "Symbols:" << std::endl << std::endl;
  
  const namespacet ns(symbol_table);

  forall_symbols(it, symbol_table.symbols)
  {
    const symbolt &symbol=it->second;
    
    languaget *ptr;
    
    if(symbol.mode=="")
      ptr=get_default_language();
    else
    {
      ptr=get_language_from_mode(symbol.mode);
      if(ptr==NULL) throw "symbol "+id2string(symbol.name)+" has unknown mode";
    }

    std::auto_ptr<languaget> p(ptr);
    std::string type_str, value_str;
    
    if(symbol.type.is_not_nil())
      p->from_type(symbol.type, type_str, ns);
    
    if(symbol.value.is_not_nil())
      p->from_expr(symbol.value, value_str, ns);
    
    if(brief)
    {
      out << symbol.name << " " << type_str << std::endl;
      continue;
    }

    out << "Symbol......: " << symbol.name << std::endl;
    out << "Pretty name.: " << symbol.pretty_name << std::endl;
    out << "Module......: " << symbol.module << std::endl;
    out << "Base name...: " << symbol.base_name << std::endl;
    out << "Mode........: " << symbol.mode << std::endl;
    out << "Type........: " << type_str << std::endl;
    out << "Value.......: " << value_str << std::endl;
    out << "Flags.......:";

    if(symbol.is_lvalue)          out << " lvalue";
    if(symbol.is_static_lifetime) out << " static_lifetime";
    if(symbol.is_thread_local)    out << " thread_local";
    if(symbol.is_file_local)      out << " file_local";
    if(symbol.is_type)            out << " type";
    if(symbol.is_extern)          out << " extern";
    if(symbol.is_input)           out << " input";
    if(symbol.is_output)          out << " output";
    if(symbol.is_macro)           out << " macro";
    if(symbol.is_parameter)       out << " parameter";
    if(symbol.is_auxiliary)       out << " auxiliary";
    if(symbol.is_property)        out << " property";
    if(symbol.is_state_var)       out << " state_var";
    if(symbol.is_exported)        out << " exported";
    if(symbol.is_volatile)        out << " volatile";

    out << std::endl;
    out << "Location....: " << symbol.location << std::endl;
    
    out << std::endl;
  }
}

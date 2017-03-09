/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_LANGAPI_LANGUAGE_UI_H
#define CPROVER_LANGAPI_LANGUAGE_UI_H

#include <util/message.h>
#include <util/language_file.h>
#include <util/symbol_table.h>
#include <util/ui_message.h>
#include <util/namespace.h>
#include <memory>

class cmdlinet;

class language_uit:public messaget
{
public:
  language_filest language_files;
  symbol_tablet symbol_table;

  language_uit(
    const cmdlinet &__cmdline,
    ui_message_handlert &ui_message_handler);
  virtual ~language_uit();

  virtual bool parse();
  virtual bool parse(const std::string &filename);
  virtual bool typecheck();
  virtual bool final();

  virtual void clear_parse()
  {
    language_files.clear();
  }

  virtual void show_symbol_table(bool brief=false);
  virtual void show_symbol_table_plain(std::ostream &out, bool brief);
  virtual void show_symbol_table_xml_ui(bool brief);
  virtual unsigned build_array_from_static_symbol_table(                         
         std::ostream &address_out,std::ostream &type_out);   

  virtual void build_entry(const namespacet ns,
      typet type, 
      std::unique_ptr<languaget> &p,
      const std::string name, 
      std::ostream &addresses,
      std::ostream &types,
      unsigned &count);

  void list_extended_symbols(const namespacet ns,const std::string symbol,
    const typet type,std::unique_ptr<languaget> &p,std::ostream &out);

  typedef ui_message_handlert::uit uit;

  uit get_ui()
  {
    return ui_message_handler.get_ui();
  }

  ui_message_handlert &ui_message_handler;

protected:
  const cmdlinet &_cmdline;
};

#endif // CPROVER_LANGAPI_LANGUAGE_UI_H

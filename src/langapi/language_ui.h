/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_LANGUAGE_UI_H
#define CPROVER_LANGUAGE_UI_H

#include <util/message.h>
#include <util/language_file.h>
#include <util/symbol_table.h>
#include <util/ui_message.h>

class cmdlinet;

class language_uit:public messaget
{
public:
  language_filest language_files;
  symbol_tablet symbol_table;
  
  language_uit(
    const std::string &program,
    const cmdlinet &__cmdline);
  virtual ~language_uit();

  virtual bool parse();
  virtual bool parse(const std::string &filename);
  virtual bool typecheck();
  virtual bool final();

  virtual void clear_parse()
  {
    language_files.clear();
  }
  
  virtual void show_symbol_table();
  virtual void show_symbol_table_plain(std::ostream &out);
  virtual void show_symbol_table_xml_ui();

  typedef ui_message_handlert::uit uit;
  
  uit get_ui()
  {
    return ui_message_handler.get_ui();
  }
  
  ui_message_handlert ui_message_handler;

protected:
  const cmdlinet &_cmdline;
};

#endif

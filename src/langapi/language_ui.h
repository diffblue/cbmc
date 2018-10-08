/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_LANGAPI_LANGUAGE_UI_H
#define CPROVER_LANGAPI_LANGUAGE_UI_H

#include <util/message.h>
#include <util/symbol_table.h>
#include <util/ui_message.h>

#include "language_file.h"

class cmdlinet;

class language_uit:public messaget
{
public:
  language_filest language_files;
  symbol_tablet symbol_table;

  language_uit(
    const cmdlinet &cmdline,
    ui_message_handlert &ui_message_handler,
    optionst *options = nullptr);
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

  typedef ui_message_handlert::uit uit;

  uit get_ui()
  {
    return ui_message_handler.get_ui();
  }

protected:
  const cmdlinet &_cmdline;
  ui_message_handlert &ui_message_handler;
  optionst *options;
};

#endif // CPROVER_LANGAPI_LANGUAGE_UI_H

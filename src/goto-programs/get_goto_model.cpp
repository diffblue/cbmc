/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "get_goto_model.h"

#include <fstream>

#include <util/message.h>
#include <util/cmdline.h>
#include <util/language_file.h>
#include <util/language.h>

#include <langapi/mode.h>

#include "read_goto_binary.h"
#include "goto_model.h"
#include "link_goto_model.h"
#include "goto_convert_functions.h"

static symbol_tablet get_source(
  const cmdlinet &cmdline,
  const std::string &filename,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  std::unique_ptr<languaget> language(
    get_language_from_filename(filename));

  if(language==nullptr)
  {
    source_locationt location;
    location.set_file(filename);
    message.error().source_location=location;
    message.error() << "failed to figure out type of file" << messaget::eom;
    throw 0;
  }

  language->set_message_handler(message_handler);
  language->get_language_options(cmdline);

  #ifdef _MSC_VER
  std::ifstream infile(widen(filename));
  #else
  std::ifstream infile(filename);
  #endif

  if(!infile)
  {
    message.error() << "failed to open input file `"
                    << filename << "'" << messaget::eom;
    throw 0;
  }

  message.status() << "Parsing " << filename << messaget::eom;

  if(language->parse(infile, filename))
  {
    message.error() << "PARSING ERROR" << messaget::eom;
    throw 0;
  }

  message.status() << "Converting" << messaget::eom;

  symbol_tablet symbol_table;
  if(language->typecheck(symbol_table, ""))
  {
    message.error() << "CONVERSION ERROR" << messaget::eom;
    throw 0;
  }

  return symbol_table;
}

void add_entry_point(
  const cmdlinet &cmdline,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::set<irep_idt> modes;

  for(const auto &it : goto_model.symbol_table.symbols)
    if(!it.second.mode.empty())
      modes.insert(it.second.mode);

  if(modes.empty())
    return;

  irep_idt final_mode=*modes.begin();

  std::unique_ptr<languaget> language(
    get_language_from_mode(final_mode));

  if(language==nullptr)
    return;

  language->set_message_handler(message_handler);
  language->get_language_options(cmdline);
  language->final(goto_model.symbol_table);

  // The above may have generated further function bodies,
  // which need to be converted.
  goto_convert(goto_model, message_handler);
}

goto_modelt get_goto_model(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  if(cmdline.args.empty())
  {
    message.error() << "Please provide a program" << messaget::eom;
    throw 0;
  }

  goto_modelt goto_model;

  // categorize
  for(const auto &filename : cmdline.args)
  {
    goto_modelt tmp_model;

    if(is_goto_binary(filename))
    {
      if(read_goto_binary(filename, tmp_model, message_handler))
        throw 0;
    }
    else
    {
      tmp_model.symbol_table=
        get_source(cmdline, filename, message_handler);
      goto_convert(tmp_model, message_handler);
    }

    // now link together
    link_goto_model(goto_model, tmp_model, message_handler);
  }

  // generate entry point
  add_entry_point(cmdline, goto_model, message_handler);

  return goto_model;
}

/*******************************************************************\

Module: Get a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Get a Goto Program

#include "initialize_goto_model.h"

#include <fstream>
#include <iostream>

#include <util/language.h>
#include <util/config.h>
#include <util/unicode.h>

#include <langapi/mode.h>
#include <langapi/language_ui.h>

#include "goto_convert_functions.h"
#include "read_goto_binary.h"

bool initialize_goto_model(
  goto_modelt &goto_model,
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  const std::vector<std::string> &files=cmdline.args;
  if(files.empty())
  {
    msg.error() << "Please provide a program" << messaget::eom;
    return true;
  }

  try
  {
    std::vector<std::string> binaries, sources;
    binaries.reserve(files.size());
    sources.reserve(files.size());

    for(const auto &file : files)
    {
      if(is_goto_binary(file))
        binaries.push_back(file);
      else
        sources.push_back(file);
    }

    if(!sources.empty())
    {
      language_filest language_files;

      language_files.set_message_handler(message_handler);

      for(const auto &filename : sources)
      {
        #ifdef _MSC_VER
        std::ifstream infile(widen(filename));
        #else
        std::ifstream infile(filename);
        #endif

        if(!infile)
        {
          msg.error() << "failed to open input file `" << filename
            << '\'' << messaget::eom;
          return true;
        }

        std::pair<language_filest::file_mapt::iterator, bool>
          result=language_files.file_map.insert(
            std::pair<std::string, language_filet>(filename, language_filet()));

        language_filet &lf=result.first->second;

        lf.filename=filename;
        lf.language=get_language_from_filename(filename);

        if(lf.language==nullptr)
        {
          source_locationt location;
          location.set_file(filename);
          msg.error().source_location=location;
          msg.error() << "failed to figure out type of file" << messaget::eom;
          return true;
        }

        languaget &language=*lf.language;
        language.set_message_handler(message_handler);
        language.get_language_options(cmdline);

        msg.status() << "Parsing " << filename << messaget::eom;

        if(language.parse(infile, filename))
        {
          msg.error() << "PARSING ERROR" << messaget::eom;
          return true;
        }

        lf.get_modules();
      }

      msg.status() << "Converting" << messaget::eom;

      if(language_files.typecheck(goto_model.symbol_table))
      {
        msg.error() << "CONVERSION ERROR" << messaget::eom;
        return true;
      }

      if(binaries.empty())
      {
        if(language_files.final(goto_model.symbol_table))
        {
          msg.error() << "CONVERSION ERROR" << messaget::eom;
          return true;
        }
      }
    }

    for(const auto &file : binaries)
    {
      msg.status() << "Reading GOTO program from file" << messaget::eom;

      if(read_object_and_link(file, goto_model, message_handler))
        return true;
    }

    msg.status() << "Generating GOTO Program" << messaget::eom;

    goto_convert(
      goto_model.symbol_table,
      goto_model.goto_functions,
      message_handler);
  }
  catch(const char *e)
  {
    msg.error() << e << messaget::eom;
    return true;
  }
  catch(const std::string e)
  {
    msg.error() << e << messaget::eom;
    return true;
  }
  catch(int)
  {
    return true;
  }
  catch(std::bad_alloc)
  {
    msg.error() << "Out of memory" << messaget::eom;
    return true;
  }

  return false; // no error
}

/*******************************************************************\

Module: Get a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>

#include <util/language.h>
#include <util/config.h>
#include <util/unicode.h>

#include <langapi/mode.h>
#include <langapi/language_ui.h>

#include "goto_convert_functions.h"
#include "read_goto_binary.h"
#include "get_goto_model.h"

/*******************************************************************\

Function: get_goto_modelt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool get_goto_modelt::operator()(const std::vector<std::string> &files)
{
  if(files.empty())
  {
    error() << "Please provide a program" << eom;
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

      language_files.set_message_handler(get_message_handler());

      for(const auto &filename : sources)
      {
        #ifdef _MSC_VER
        std::ifstream infile(widen(filename));
        #else
        std::ifstream infile(filename);
        #endif

        if(!infile)
        {
          error() << "failed to open input file `" << filename
                  << '\'' << eom;
          return true;
        }

        std::pair<language_filest::file_mapt::iterator, bool>
          result=language_files.file_map.insert(
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
          error() << "PARSING ERROR" << eom;
          return true;
        }

        lf.get_modules();
      }

      status() << "Converting" << eom;

      if(language_files.typecheck(symbol_table))
      {
        error() << "CONVERSION ERROR" << eom;
        return true;
      }

      if(binaries.empty())
      {
        if(language_files.final(symbol_table))
        {
          error() << "CONVERSION ERROR" << eom;
          return true;
        }
      }
    }

    for(const auto &file : binaries)
    {
      status() << "Reading GOTO program from file" << eom;

      if(read_object_and_link(file, *this, get_message_handler()))
        return true;
    }

    if(!binaries.empty())
      config.set_from_symbol_table(symbol_table);

    status() << "Generating GOTO Program" << eom;

    goto_convert(symbol_table,
                 goto_functions,
                 get_message_handler());
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }

  return false; // no error
}

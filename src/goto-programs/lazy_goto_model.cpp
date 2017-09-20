// Copyright 2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Model for lazy loading of functions

#include "lazy_goto_model.h"
#include "read_goto_binary.h"
#include "rebuild_goto_start_function.h"

#include <langapi/mode.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/language.h>
#include <util/unicode.h>

#include <fstream>

lazy_goto_modelt::lazy_goto_modelt(message_handlert &message_handler)
  : goto_model(new goto_modelt()),
    symbol_table(goto_model->symbol_table),
    goto_functions(goto_model->goto_functions)
{
  language_files.set_message_handler(message_handler);
}

lazy_goto_modelt::lazy_goto_modelt(lazy_goto_modelt &&other)
  : goto_model(std::move(other.goto_model)),
    language_files(std::move(other.language_files)),
    symbol_table(goto_model->symbol_table),
    goto_functions(goto_model->goto_functions)
{
}

void lazy_goto_modelt::initialize(const cmdlinet &cmdline)
{
  messaget msg(language_files.get_message_handler());

  const std::vector<std::string> &files=cmdline.args;
  if(files.empty())
  {
    msg.error() << "Please provide a program" << messaget::eom;
    throw 0;
  }

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
        throw 0;
      }

      std::pair<language_filest::file_mapt::iterator, bool> result =
        language_files.file_map.emplace(filename, language_filet());

      language_filet &lf=result.first->second;

      lf.filename=filename;
      lf.language=get_language_from_filename(filename);

      if(lf.language==nullptr)
      {
        source_locationt location;
        location.set_file(filename);
        msg.error().source_location=location;
        msg.error() << "failed to figure out type of file" << messaget::eom;
        throw 0;
      }

      languaget &language=*lf.language;
      language.set_message_handler(language_files.get_message_handler());
      language.get_language_options(cmdline);

      msg.status() << "Parsing " << filename << messaget::eom;

      if(language.parse(infile, filename))
      {
        msg.error() << "PARSING ERROR" << messaget::eom;
        throw 0;
      }

      lf.get_modules();
    }

    msg.status() << "Converting" << messaget::eom;

    if(language_files.typecheck(symbol_table))
    {
      msg.error() << "CONVERSION ERROR" << messaget::eom;
      throw 0;
    }
  }

  for(const auto &file : binaries)
  {
    msg.status() << "Reading GOTO program from file" << messaget::eom;

    if(read_object_and_link(
      file, symbol_table, goto_functions, msg.get_message_handler()))
    {
      throw 0;
    }
  }

  bool binaries_provided_start =
    symbol_table.has_symbol(goto_functionst::entry_point());

  bool entry_point_generation_failed=false;

  if(binaries_provided_start && cmdline.isset("function"))
  {
    // Rebuild the entry-point, using the language annotation of the
    // existing __CPROVER_start function:
    rebuild_lazy_goto_start_functiont rebuild_existing_start(
      cmdline, *this, msg.get_message_handler());
    entry_point_generation_failed=rebuild_existing_start();
  }
  else if(!binaries_provided_start)
  {
    // Unsure of the rationale for only generating stubs when there are no
    // GOTO binaries in play; simply mirroring old code in language_uit here.
    if(binaries.empty())
    {
      // Enable/disable stub generation for opaque methods
      bool stubs_enabled=cmdline.isset("generate-opaque-stubs");
      language_files.set_should_generate_opaque_method_stubs(stubs_enabled);
    }

    // Allow all language front-ends to try to provide the user-specified
    // (--function) entry-point, or some language-specific default:
    entry_point_generation_failed=
      language_files.generate_support_functions(symbol_table);
  }

  if(entry_point_generation_failed)
  {
    msg.error() << "SUPPORT FUNCTION GENERATION ERROR" << messaget::eom;
    throw 0;
  }

  if(language_files.final(symbol_table))
  {
    msg.error() << "FINAL STAGE CONVERSION ERROR" << messaget::eom;
    throw 0;
  }

  // stupid hack
  config.set_object_bits_from_symbol_table(symbol_table);
}

/// Eagerly loads all functions from the symbol table.
void lazy_goto_modelt::load_all_functions()
{
  goto_convert(*goto_model, language_files.get_message_handler());
  // As lazy goto functions are no longer required language files is done with
  language_files.clear();
}

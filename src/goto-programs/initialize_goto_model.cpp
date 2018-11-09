/*******************************************************************\

Module: Get a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Get a Goto Program

#include "initialize_goto_model.h"

#include <fstream>
#include <iostream>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/message.h>
#include <util/unicode.h>

#include <langapi/mode.h>
#include <langapi/language.h>

#include <goto-programs/rebuild_goto_start_function.h>
#include <util/exception_utils.h>

#include "goto_convert_functions.h"
#include "read_goto_binary.h"

goto_modelt initialize_goto_model(
  const cmdlinet &cmdline,
  message_handlert &message_handler,
  const optionst &options)
{
  messaget msg(message_handler);
  const std::vector<std::string> &files=cmdline.args;
  if(files.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "missing program argument",
      "filename",
      "one or more paths to program files");
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

  language_filest language_files;
  language_files.set_message_handler(message_handler);

  goto_modelt goto_model;

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
        throw system_exceptiont(
          "Failed to open input file `" + filename + '\'');
      }

      language_filet &lf=language_files.add_file(filename);
      lf.language=get_language_from_filename(filename);

      if(lf.language==nullptr)
      {
        throw invalid_source_file_exceptiont(
          "Failed to figure out type of file `" + filename + '\'');
      }

      languaget &language=*lf.language;
      language.set_message_handler(message_handler);
      language.set_language_options(options);

      msg.status() << "Parsing " << filename << messaget::eom;

      if(language.parse(infile, filename))
      {
        throw invalid_source_file_exceptiont("PARSING ERROR");
      }

      lf.get_modules();
    }

    msg.status() << "Converting" << messaget::eom;

    if(language_files.typecheck(goto_model.symbol_table))
    {
      throw invalid_source_file_exceptiont("CONVERSION ERROR");
    }
  }

  for(const auto &file : binaries)
  {
    msg.status() << "Reading GOTO program from file" << messaget::eom;

    if(read_object_and_link(file, goto_model, message_handler))
    {
      throw invalid_source_file_exceptiont(
        "failed to read object or link in file `" + file + '\'');
    }
  }

  bool binaries_provided_start=
    goto_model.symbol_table.has_symbol(goto_functionst::entry_point());

  bool entry_point_generation_failed=false;

  if(binaries_provided_start && cmdline.isset("function"))
  {
    // Rebuild the entry-point, using the language annotation of the
    // existing __CPROVER_start function:
    rebuild_goto_start_functiont rebuild_existing_start(
      options, goto_model, msg.get_message_handler());
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
      language_files.generate_support_functions(goto_model.symbol_table);
  }

  if(entry_point_generation_failed)
  {
    throw invalid_source_file_exceptiont("SUPPORT FUNCTION GENERATION ERROR");
  }

  if(language_files.final(goto_model.symbol_table))
  {
    throw invalid_source_file_exceptiont("FINAL STAGE CONVERSION ERROR");
  }

  msg.status() << "Generating GOTO Program" << messaget::eom;

  goto_convert(
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);

  if(cmdline.isset("validate-goto-model"))
  {
    goto_model.validate(validation_modet::EXCEPTION);
  }

  // stupid hack
  config.set_object_bits_from_symbol_table(
    goto_model.symbol_table);

  return goto_model;
}

/*******************************************************************\

Module: Get a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Get a Goto Program

#include "initialize_goto_model.h"

#include <fstream>

#include <util/config.h>
#include <util/message.h>
#include <util/options.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <langapi/language.h>
#include <langapi/language_file.h>
#include <langapi/mode.h>

#include <goto-programs/rebuild_goto_start_function.h>
#include <util/exception_utils.h>

#include "goto_convert_functions.h"
#include "read_goto_binary.h"

/// Generate an entry point that calls a function with the given name, based on
/// the functions language mode in the symbol table
static bool generate_entry_point_for_function(
  const irep_idt &entry_function_name,
  const optionst &options,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  auto const entry_function_sym =
    goto_model.symbol_table.lookup(entry_function_name);
  if(entry_function_sym == nullptr)
  {
    throw invalid_command_line_argument_exceptiont{
      // NOLINTNEXTLINE(whitespace/braces)
      std::string{"couldn't find function with name '"} +
        id2string(entry_function_name) + "' in symbol table",
      "--function"};
  }
  PRECONDITION(!entry_function_sym->mode.empty());
  auto const entry_language = get_language_from_mode(entry_function_sym->mode);
  CHECK_RETURN(entry_language != nullptr);
  entry_language->set_message_handler(message_handler);
  entry_language->set_language_options(options);
  return entry_language->generate_support_functions(goto_model.symbol_table);
}

goto_modelt initialize_goto_model(
  const std::vector<std::string> &files,
  message_handlert &message_handler,
  const optionst &options)
{
  messaget msg(message_handler);
  if(files.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "missing program argument",
      "filename",
      "one or more paths to program files");
  }

  std::list<std::string> binaries, sources;

  for(const auto &file : files)
  {
    if(is_goto_binary(file, message_handler))
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
          "Failed to open input file '" + filename + '\'');
      }

      language_filet &lf=language_files.add_file(filename);
      lf.language=get_language_from_filename(filename);

      if(lf.language==nullptr)
      {
        throw invalid_source_file_exceptiont(
          "Failed to figure out type of file '" + filename + '\'');
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

  if(read_objects_and_link(binaries, goto_model, message_handler))
  {
    throw invalid_source_file_exceptiont{
      "failed to read object or link in files"};
  }

  bool binaries_provided_start=
    goto_model.symbol_table.has_symbol(goto_functionst::entry_point());

  bool entry_point_generation_failed=false;

  if(binaries_provided_start && options.is_set("function"))
  {
    // Get the language annotation of the existing __CPROVER_start function.
    std::unique_ptr<languaget> language = get_entry_point_language(
      goto_model.symbol_table, options, message_handler);

    // To create a new entry point we must first remove the old one
    remove_existing_entry_point(goto_model.symbol_table);

    // Create the new entry-point
    entry_point_generation_failed =
      language->generate_support_functions(goto_model.symbol_table);

    // Remove the function from the goto functions so it is copied back in
    // from the symbol table during goto_convert
    if(!entry_point_generation_failed)
      goto_model.unload(goto_functionst::entry_point());
  }
  else if(!binaries_provided_start)
  {
    if(options.is_set("function"))
    {
      // no entry point is present; Use the mode of the specified entry function
      // to generate one
      entry_point_generation_failed = generate_entry_point_for_function(
        options.get_option("function"), options, goto_model, message_handler);
    }
    if(entry_point_generation_failed || !options.is_set("function"))
    {
      // Allow all language front-ends to try to provide the user-specified
      // (--function) entry-point, or some language-specific default:
      entry_point_generation_failed =
        language_files.generate_support_functions(goto_model.symbol_table);
    }
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

  if(options.is_set("validate-goto-model"))
  {
    goto_model_validation_optionst goto_model_validation_options{
      goto_model_validation_optionst ::set_optionst::all_false};

    goto_model.validate(
      validation_modet::INVARIANT, goto_model_validation_options);
  }

  // stupid hack
  config.set_object_bits_from_symbol_table(
    goto_model.symbol_table);

  return goto_model;
}

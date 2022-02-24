/******************************************************************\

Module: symtab2gb_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#include "symtab2gb_parse_options.h"

#include <fstream>
#include <iostream>
#include <string>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/write_goto_binary.h>

#include <json-symtab-language/json_symtab_language.h>
#include <langapi/mode.h>

#include <linking/linking.h>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/version.h>

symtab2gb_parse_optionst::symtab2gb_parse_optionst(int argc, const char *argv[])
  : parse_options_baset{SYMTAB2GB_OPTIONS,
                        argc,
                        argv,
                        std::string("SYMTAB2GB ") + CBMC_VERSION}
{
}

static inline bool failed(bool error_indicator)
{
  return error_indicator;
}

static void run_symtab2gb(
  const std::vector<std::string> &symtab_filenames,
  const std::string &gb_filename)
{
  // try opening all the files first to make sure we can
  // even read/write what we want
  std::ofstream out_file{gb_filename, std::ios::binary};
  if(!out_file.is_open())
  {
    throw system_exceptiont{"couldn't open output file '" + gb_filename + "'"};
  }
  std::vector<std::ifstream> symtab_files;
  for(auto const &symtab_filename : symtab_filenames)
  {
    std::ifstream symtab_file{symtab_filename};
    if(!symtab_file.is_open())
    {
      throw system_exceptiont{"couldn't open input file '" + symtab_filename +
                              "'"};
    }
    symtab_files.emplace_back(std::move(symtab_file));
  }

  stream_message_handlert message_handler{std::cerr};

  auto const symtab_language = new_json_symtab_language();
  symtab_language->set_message_handler(message_handler);

  symbol_tablet linked_symbol_table;

  for(std::size_t ix = 0; ix < symtab_files.size(); ++ix)
  {
    auto const &symtab_filename = symtab_filenames[ix];
    auto &symtab_file = symtab_files[ix];
    if(failed(symtab_language->parse(symtab_file, symtab_filename)))
    {
      throw invalid_source_file_exceptiont{
        "failed to parse symbol table from file '" + symtab_filename + "'"};
    }
    symbol_tablet symtab{};
    if(failed(symtab_language->typecheck(symtab, "<unused>")))
    {
      throw invalid_source_file_exceptiont{
        "failed to typecheck symbol table from file '" + symtab_filename + "'"};
    }
    config.set_from_symbol_table(symtab);

    if(failed(linking(linked_symbol_table, symtab, message_handler)))
    {
      throw invalid_input_exceptiont{
        "failed to link `" + symtab_filename + "'"};
    }
  }

  goto_modelt linked_goto_model;
  linked_goto_model.symbol_table.swap(linked_symbol_table);
  goto_convert(linked_goto_model, message_handler);

  if(failed(write_goto_binary(out_file, linked_goto_model)))
  {
    throw system_exceptiont{"failed to write goto binary to " + gb_filename};
  }
}

void symtab2gb_parse_optionst::register_languages()
{
  // As this is a converter and linker it only really needs to support
  // the JSON symtab front-end.
  register_language(new_json_symtab_language);
  // Workaround to allow external front-ends to use "C" mode
  register_language(new_ansi_c_language);
}

int symtab2gb_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    log.status() << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }
  if(cmdline.args.empty())
  {
    throw invalid_command_line_argument_exceptiont{
      "expect at least one input file", "<json-symtab-file>"};
  }
  std::vector<std::string> symtab_filenames = cmdline.args;
  std::string gb_filename = "a.out";
  if(cmdline.isset(SYMTAB2GB_OUT_FILE_OPT))
  {
    gb_filename = cmdline.get_value(SYMTAB2GB_OUT_FILE_OPT);
  }
  register_languages();
  config.set(cmdline);
  run_symtab2gb(symtab_filenames, gb_filename);
  return CPROVER_EXIT_SUCCESS;
}

void symtab2gb_parse_optionst::help()
{
  log.status()
    << '\n'
    << banner_string("symtab2gb", CBMC_VERSION) << '\n'
    << align_center_with_border("Copyright (C) 2019") << '\n'
    << align_center_with_border("Diffblue Ltd.") << '\n'
    << align_center_with_border("info@diffblue.com") << '\n'
    << '\n'
    << "Usage:                                   Purpose:\n"
    << '\n'
    << "symtab2gb [-?] [-h] [--help]             show help\n"
       "symtab2gb                                compile .json_symtabs\n"
       "  <json-symtab-file>+                    to a single goto-binary\n"
       "  [--out <outfile>]\n\n"
       "<json-symtab-file>                       a CBMC symbol table in\n"
       "                                         JSON format\n"
       "--out <outfile>                          specify the filename of\n"
       "                                         the resulting binary\n"
       "                                         (default: a.out)\n"
    << messaget::eom;
}

// Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// Commandline parser for the memory analyzer executing main work.

#ifdef __linux__

#include "memory_analyzer_parse_options.h"
#include "analyze_symbol.h"
#include "gdb_api.h"

#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <util/config.h>
#include <util/exit_codes.h>
#include <util/message.h>
#include <util/string_utils.h>

int memory_analyzer_parse_optionst::doit()
{
  // This script is the entry point and has to make sure
  // that the config object is set to a valid architecture.
  // config is later used to determine right size for types.
  // If config is not set, you might see a bunch of types with
  // size 0.
  // It might be desierable to convert this into flags in the future.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();

  if(cmdline.args.size() != 1)
  {
    error() << "Please provide one binary with symbols to process" << eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  std::string binary = cmdline.args[0];

  gdb_apit gdb_api = gdb_apit(binary.c_str());
  gdb_api.create_gdb_process();

  if(cmdline.isset("core-file"))
  {
    std::string core_file = cmdline.get_value("core-file");
    gdb_api.run_gdb_from_core(core_file);
  }
  else if(cmdline.isset("breakpoint"))
  {
    std::string breakpoint = cmdline.get_value("breakpoint");
    gdb_api.run_gdb_to_breakpoint(breakpoint);
  }
  else
  {
    error() << "Either the 'core-file' or 'breakpoint; flag must be provided\n"
            << "Cannot execute memory-analyzer. Going to shut it down...\n"
            << messaget::eom;

    gdb_api.terminate_gdb_process();

    help();
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if(cmdline.isset("symbols"))
  {
    const std::string symbol_list(cmdline.get_value("symbols"));
    std::vector<std::string> result;
    split_string(symbol_list, ',', result, false, false);

    goto_modelt goto_model;
    read_goto_binary(binary, goto_model, ui_message_handler);

    symbol_analyzert analyzer(
      goto_model.symbol_table, gdb_api, ui_message_handler);

    for(auto it = result.begin(); it != result.end(); it++)
    {
      messaget::result() << "analyzing symbol: " << (*it) << "\n";
      analyzer.analyse_symbol(*it);
    }

    messaget::result() << "GENERATED CODE: \n" << messaget::eom;
    messaget::result() << analyzer.get_code() << "\n" << messaget::eom;

    gdb_api.terminate_gdb_process();
    return CPROVER_EXIT_SUCCESS;
  }
  else
  {
    error() << "It is required to provide the symbols flag in order to make "
            << "this tool work.\n"
            << messaget::eom;
  }
  gdb_api.terminate_gdb_process();
  help();
  return CPROVER_EXIT_USAGE_ERROR;
}

void memory_analyzer_parse_optionst::help()
{
}

#endif // __linux__

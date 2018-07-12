// Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// This code does the command line parsing for the memory-analyzer tool

#ifndef CPROVER_MEMORY_ANALYZER_MEMORY_ANALYZER_PARSE_OPTIONS_H
#define CPROVER_MEMORY_ANALYZER_MEMORY_ANALYZER_PARSE_OPTIONS_H
#ifdef __linux__
#include <util/parse_options.h>
#include <util/ui_message.h>

// clang-format off
#define MEMMORY_ANALYZER_OPTIONS \
  "(core-file):" \
  "(breakpoint):" \
  "(symbols):"

// clang-format on

class memory_analyzer_parse_optionst : public parse_options_baset,
                                       public messaget
{
public:
  int doit() override;
  void help() override;

  memory_analyzer_parse_optionst(int argc, const char **argv)
    : parse_options_baset(MEMMORY_ANALYZER_OPTIONS, argc, argv),
      messaget(ui_message_handler),
      ui_message_handler(cmdline, "memory-analyzer")
  {
  }

protected:
  ui_message_handlert ui_message_handler;
};
#endif // __linux__
#endif // CPROVER_MEMORY_ANALYZER_MEMORY_ANALYZER_PARSE_OPTIONS_H

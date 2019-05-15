/*******************************************************************\

Module: Memory Analyzer

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

/// \file
/// This code does the command line parsing for the memory-analyzer tool

#ifndef CPROVER_MEMORY_ANALYZER_MEMORY_ANALYZER_PARSE_OPTIONS_H
#define CPROVER_MEMORY_ANALYZER_MEMORY_ANALYZER_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/ui_message.h>

// clang-format off
#define MEMORY_ANALYZER_OPTIONS \
  "(version)" \
  "(json-ui)" \
  "(core-file):" \
  "(breakpoint):" \
  "(symbols):" \
  "(symtab-snapshot)" \
  "(output-file):"
// clang-format on

class memory_analyzer_parse_optionst : public parse_options_baset
{
public:
  memory_analyzer_parse_optionst(int argc, const char *argv[]);

  int doit() override;
  void help() override;

protected:
  messaget message;
};

#endif // CPROVER_MEMORY_ANALYZER_MEMORY_ANALYZER_PARSE_OPTIONS_H

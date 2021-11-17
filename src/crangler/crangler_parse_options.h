/*******************************************************************\

Module: CRANGLER Command Line Option Processing

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// CRANGLER Command Line Option Processing

#ifndef CPROVER_CRANGLER_CRANGLER_PARSE_OPTIONS_H
#define CPROVER_CRANGLER_CRANGLER_PARSE_OPTIONS_H

#include <util/parse_options.h>

class crangler_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  crangler_parse_optionst(int argc, const char **argv)
    : parse_options_baset("", argc, argv, "CRANGLER")
  {
  }

protected:
  void process_crangler_json(const std::string &file_name);
};

#endif // CPROVER_CRANGLER_CRANGLER_PARSE_OPTIONS_H

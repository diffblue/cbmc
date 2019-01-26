/******************************************************************\

Module: goto_harness_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H
#define CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H

#include <util/parse_options.h>

#define GOTO_HARNESS_OPTIONS "(version)" // end GOTO_HARNESS_OPTIONS

class goto_harness_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  goto_harness_parse_optionst(int argc, const char *argv[]);
};

#endif // CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H

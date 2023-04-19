// Author: Fotis Koutoulakis for Diffblue Ltd.

#ifndef CPROVER_GOTO_INSPECT_GOTO_INSPECT_PARSE_OPTIONS_H
#define CPROVER_GOTO_INSPECT_GOTO_INSPECT_PARSE_OPTIONS_H

#include <util/parse_options.h>

// clang-format off
#define GOTO_INSPECT_OPTIONS                                                   \
  "(version)"                                                                  \
  "(show-goto-functions)"                                                      \
// end GOTO_INSPECT_OPTIONS

// clang-format on

struct goto_inspect_parse_optionst : public parse_options_baset
{
  int doit() override;
  void help() override;

  goto_inspect_parse_optionst(int argc, const char *argv[]);
};

#endif // CPROVER_GOTO_INSPECT_GOTO_INSPECT_PARSE_OPTIONS_H

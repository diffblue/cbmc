// Author: Fotis Koutoulakis for Diffblue Ltd.

#ifndef CPROVER_GOTO_BMC_GOTO_BMC_PARSE_OPTIONS_H
#define CPROVER_GOTO_BMC_GOTO_BMC_PARSE_OPTIONS_H

#include <util/parse_options.h>

#include <libcprover-cpp/api_options.h>

#include <memory>
#include <string>
#include <vector>

// clang-format off
#define GOTO_BMC_OPTIONS \
  "(version)"
// clang-format on

class goto_bmc_parse_optionst : public parse_options_baset
{
public:
  goto_bmc_parse_optionst(int argc, const char **argv);

  void help() override;

  int doit() override;
};

#endif // CPROVER_GOTO_BMC_GOTO_BMC_PARSE_OPTIONS_H

/// \file
/// \author Diffblue Ltd.

#ifndef CPROVER_GOTO_UNWIND_SRC_GOTO_UNWIND_PARSE_OPTIONS_H
#define CPROVER_GOTO_UNWIND_SRC_GOTO_UNWIND_PARSE_OPTIONS_H

#include <string>

#include <goto-programs/goto_model.h>
#include <util/parse_options.h>

class goto_unwind_parse_optionst : public parse_options_baset
{
public:
  goto_unwind_parse_optionst(int argc, const char **argv);

  int doit() override;
  void help() override;
  goto_modelt get_goto_model(const std::string &goto_binary_path);
  void do_unwind(goto_modelt &model, size_t limit);
};

#endif

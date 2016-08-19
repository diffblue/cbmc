/*******************************************************************\

Module: GOTO-DIFF Command Line Option Processing

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_GOTO_DIFF_PARSEOPTIONS_H
#define CPROVER_GOTO_DIFF_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>

#include <goto-programs/goto_model.h>

class goto_modelt;
class optionst;

#define GOTO_DIFF_OPTIONS \
  "(json-ui)" \
  "(show-goto-functions)" \
  "(verbosity):(version)" \
  "u(unified)(change-impact)(forward-impact)(backward-impact)" \
  "(compact-output)"

class goto_diff_parse_optionst:
  public parse_options_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  goto_diff_parse_optionst(int argc, const char **argv);
  goto_diff_parse_optionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

protected:
  virtual void register_languages();

  virtual void get_command_line_options(optionst &options);

  virtual int get_goto_programs(
    const optionst &options,
    goto_modelt &goto_model1,
    goto_modelt &goto_model2);

  virtual bool process_goto_program(
    const optionst &options,
    goto_modelt &goto_model);
    
  void eval_verbosity();
  
  void preprocessing();
};

#endif

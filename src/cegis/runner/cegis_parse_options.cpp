/*******************************************************************\

Module: CEGIS Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <cbmc/version.h>
#include <util/mp_arith.h>
#include <util/options.h>

#include <cegis/options/parameters.h>
#include <cegis/danger/facade/danger_runner.h>
#include <cegis/safety/facade/safety_runner.h>
#include <cegis/jsa/facade/jsa_runner.h>
#include <cegis/control/facade/control_runner.h>
#include <cegis/refactor/facade/refactor_runner.h>

#include <cegis/runner/cegis_parse_options.h>

/*******************************************************************\

Function: cegis_parse_optionst::cegis_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cegis_parse_optionst::cegis_parse_optionst(int argc, const char **argv):
  cbmc_parse_optionst(argc, argv, CEGIS_OPTIONS)
{
}

namespace
{
void set_integer_option(optionst &opt, const cmdlinet &cmd,
    const char * const name, const unsigned int default_value)
{
  if(!cmd.isset(name)) return opt.set_option(name, default_value);
  const std::string text_value(cmd.get_value(name));
  const mp_integer::ullong_t value=string2integer(text_value).to_ulong();
  opt.set_option(name, static_cast<unsigned int>(value));
}
}

/*******************************************************************\

Function: cegis_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegis_parse_optionst::get_command_line_options(optionst &options)
{
  cbmc_parse_optionst::get_command_line_options(options);

  const bool configure_cegis=cmdline.isset("danger") || cmdline.isset("safety")
      || cmdline.isset("jsa") || cmdline.isset(CEGIS_CONTROL)
      || cmdline.isset(CEGIS_REFACTOR);
  if(configure_cegis)
  {
    set_integer_option(options, cmdline, "cegis-min-size", 1u);
    set_integer_option(options, cmdline, "cegis-max-size", 5u);
    options.set_option("cegis-parallel-verify", cmdline.isset("cegis-parallel-verify"));
    options.set_option("cegis-limit-wordsize", cmdline.isset("cegis-limit-wordsize"));
    options.set_option("cegis-match-select", !cmdline.isset("cegis-tournament-select"));
    options.set_option("cegis-statistics", cmdline.isset("cegis-statistics"));
    options.set_option(CEGIS_GENETIC, cmdline.isset(CEGIS_GENETIC));
    options.set_option(CEGIS_GENETIC_ONLY, cmdline.isset(CEGIS_GENETIC_ONLY));
    set_integer_option(options, cmdline, "cegis-genetic-rounds", 10u);
    set_integer_option(options, cmdline, "cegis-seed", 747864937u);
    set_integer_option(options, cmdline, "cegis-genetic-popsize", 2000u);
    set_integer_option(options, cmdline, "cegis-genetic-mutation-rate", 1u);
    set_integer_option(options, cmdline, "cegis-genetic-replace-rate", 15u);
    options.set_option("danger-no-ranking", cmdline.isset("danger-no-ranking"));
    set_integer_option(options, cmdline, CEGIS_SYMEX_HEAD_START, 0u);
    options.set_option(CEGIS_SHOW_ITERATIONS, cmdline.isset(CEGIS_SHOW_ITERATIONS));
    options.set_option(CEGIS_KEEP_GOTO_PROGRAMS, cmdline.isset(CEGIS_KEEP_GOTO_PROGRAMS));
    set_integer_option(options, cmdline, CEGIS_MAX_RUNTIME, 300u);
    options.set_option(CEGIS_NULL_OBJECT_REFACTOR, cmdline.isset(CEGIS_NULL_OBJECT_REFACTOR));
  }
}

/*******************************************************************\

Function: cegis_parse_optionst::do_bmc

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int cegis_parse_optionst::do_bmc(
  bmct &bmc,
  const goto_functionst &goto_functions)
{
  optionst options;
  get_command_line_options(options);

  if(cmdline.isset("danger"))
    return run_danger(options, result(), symbol_table, goto_functions);
  if(cmdline.isset("safety"))
    return run_safety(options, result(), symbol_table, goto_functions);
  if(cmdline.isset("jsa"))
    return run_jsa(options, result(), symbol_table, goto_functions);
  if(cmdline.isset(CEGIS_CONTROL))
    return run_control(options, result(), symbol_table, goto_functions);
  if(cmdline.isset(CEGIS_REFACTOR))
    return run_refactor(options, result(), symbol_table, goto_functions);

  return cbmc_parse_optionst::do_bmc(bmc, goto_functions);
}

/*******************************************************************\

Function: cegis_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: print help

\*******************************************************************/

void cegis_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *   CEGIS " CBMC_VERSION " - Copyright (C) 2015-2016 ";

  std::cout << "(" << (sizeof(void *)*8) << "-bit version)";

  std::cout << "  * *\n";

  std::cout <<
    "* *       Matt Lewis, Pascal Kesseli, Daniel Kroening       * *\n"
    "* *    University of Oxford, Computer Science Department    * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                                Purpose:\n"
    "\n"
    " cegis [-?] [-h] [--help]              show help\n"
    " cegis [--danger|--safety] file.c ...  source file names\n"
    "\n"
    "Invariant options:\n"
    " --danger                              synthesise danger invariant\n"
    " --safety                              synthesise safety invariant\n"
    "\n"
    "GA options:\n"
    " --cegis-genetic                       use symex and genetic back-end\n"
    " --cegis-match-select                  use \"match\" genetic selector\n"
    " --cegis-tournament-select             use \"tournament\" genetic selector\n"
    " --cegis-genetic-rounds                number of wheel rounds per evolution step\n"
    " --cegis-genetic-popsize               population size\n"
    " --cegis-genetic-mutation-rate         likelihood of mutation (1-100)\n"
    " --cegis-genetic-replace-rate          evolutionary pressure (1-100)\n"
    "\n"
    "Output options:\n"
    " --cegis-statistics                    show runtime and CEGIS statistics\n"
    " --cegis-keep-goto-programs            keep generated GOTO programs\n"
    " --cegis-show-iterations               show intermediate solutions in CEGIS loop\n"
    "\n"
    "Experiment options:\n"
    " --cegis-max-runtime                   maximum runtime timeout\n"
    " --cegis-min-size                      minimum solution length to consider\n"
    " --cegis-max-size                      maximum solution length to consider\n"
    " --cegis-parallel-verify               find multiple counterexamples concurrently\n"
    " --cegis-limit-wordsize                allow inductive conjecture with limited word size\n"
    " --cegis-seed                          starting seed for random number generator\n"
    " --danger-no-ranking                   use total danger invariants\n"
    " --cegis-symex-head-start              number of iterations head-start for symex over GA \n"
    "\n";
}

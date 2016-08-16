/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/mp_arith.h>
#include <util/options.h>

#include <cegis/options/parameters.h>
#include <cegis/danger/facade/danger_runner.h>
#include <cegis/safety/facade/safety_runner.h>
#include <cegis/jsa/facade/jsa_runner.h>

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

/*******************************************************************\

Function: cegis_parse_optionst::~cegis_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cegis_parse_optionst::~cegis_parse_optionst()
{
}

namespace
{
void set_integer_option(optionst &opt, const cmdlinet &cmd,
    const char * const name, const unsigned int default_value)
{
  if (!cmd.isset(name)) return opt.set_option(name, default_value);
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

  if(cmdline.isset("danger") || cmdline.isset("safety") || cmdline.isset("jsa"))
  {
    set_integer_option(options, cmdline, "cegis-min-size", 1u);
    set_integer_option(options, cmdline, "cegis-max-size", 5u);
    options.set_option("cegis-parallel-verify", cmdline.isset("cegis-parallel-verify"));
    options.set_option("cegis-limit-wordsize", cmdline.isset("cegis-limit-wordsize"));
    options.set_option("cegis-match-select", !cmdline.isset("cegis-tournament-select"));
    options.set_option("cegis-statistics", cmdline.isset("cegis-statistics"));
    options.set_option(CEGIS_GENETIC, cmdline.isset(CEGIS_GENETIC));
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

  return cbmc_parse_optionst::do_bmc(bmc, goto_functions);
}

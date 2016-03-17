/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/mp_arith.h>
#include <util/options.h>

#include <cegis/danger/facade/danger_runner.h>
#include <cegis/safety/facade/safety_runner.h>

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

/*******************************************************************\

Function: cegis_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegis_parse_optionst::get_command_line_options(optionst &options)
{
  cbmc_parse_optionst::get_command_line_options(options);

  if(cmdline.isset("danger") || cmdline.isset("safety"))
  {
    unsigned int min_prog_size=1u;
    if (cmdline.isset("cegis-min-size"))
      min_prog_size=string2integer(cmdline.get_value("cegis-min-size")).to_ulong();
    options.set_option("cegis-min-size", min_prog_size);
    unsigned int max_prog_size=5u;
    if (cmdline.isset("cegis-max-size"))
      max_prog_size=string2integer(cmdline.get_value("cegis-max-size")).to_ulong();
    options.set_option("cegis-max-size", max_prog_size);
    options.set_option("cegis-parallel-verify", cmdline.isset("cegis-parallel-verify"));
    options.set_option("cegis-limit-wordsize", cmdline.isset("cegis-limit-wordsize"));
    options.set_option("cegis-match-select", !cmdline.isset("cegis-tournament-select"));
    options.set_option("cegis-statistics", cmdline.isset("cegis-statistics"));
    options.set_option("cegis-genetic", cmdline.isset("cegis-genetic"));
    unsigned int genetic_rounds=10u;
    if (cmdline.isset("cegis-genetic-rounds"))
      genetic_rounds=string2integer(cmdline.get_value("cegis-genetic-rounds")).to_ulong();
    options.set_option("cegis-genetic-rounds", genetic_rounds);
    unsigned int seed=747864937u;
    if (cmdline.isset("cegis-seed"))
      seed=string2integer(cmdline.get_value("cegis-seed")).to_ulong();
    options.set_option("cegis-seed", seed);
    unsigned int pop_size=2000u;
    if (cmdline.isset("cegis-genetic-popsize"))
      pop_size=string2integer(cmdline.get_value("cegis-genetic-popsize")).to_ulong();
    options.set_option("cegis-genetic-popsize", pop_size);
    unsigned int mutation_rate=1u;
    if (cmdline.isset("cegis-genetic-mutation-rate"))
      mutation_rate=string2integer(cmdline.get_value("cegis-genetic-mutation-rate")).to_ulong();
    options.set_option("cegis-genetic-mutation-rate", mutation_rate);
    unsigned int replace_rate=15u;
    if (cmdline.isset("cegis-genetic-replace-rate"))
      replace_rate=string2integer(cmdline.get_value("cegis-genetic-replace-rate")).to_ulong();
    options.set_option("cegis-genetic-replace-rate", replace_rate);
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

  return cbmc_parse_optionst::do_bmc(bmc, goto_functions);
}

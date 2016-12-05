/*******************************************************************\

Module: CBMC/CEGIS Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGIS_RUNNER_CEGIS_PARSE_OPTIONS_H
#define CPROVER_CEGIS_RUNNER_CEGIS_PARSE_OPTIONS_H

#include <cbmc/cbmc_parse_options.h>

#define CEGIS_OPTIONS \
  "(cegis)(cegis-seed):(cegis-root):(cegis-targets):" \
  "(cegis-min-prog-size):(cegis-max-prog-size):(cegis-skolem):(cegis-ranking):" \
  "(cegis-max-size):(cegis-statistics)(cegis-show-iterations)" \
  "(cegis-keep-goto-programs)(cegis-genetic)(cegis-genetic-only)(cegis-genetic-rounds):" \
  "(cegis-genetic-popsize):(cegis-tournament-select)" \
  "(cegis-genetic-mutation-rate):(cegis-genetic-replace-rate):" \
  "(cegis-limit-wordsize)(cegis-parallel-verify)(cegis-symex-head-start):" \
  "(safety)(danger)(jsa)(danger-max-size):(danger-no-ranking)" \
  "(cegis-control)" \
  "(cegis-refactor)(cegis-refactor-null-object)"

class cegis_parse_optionst: public cbmc_parse_optionst
{
public:
  cegis_parse_optionst(int argc, const char **argv);
  virtual ~cegis_parse_optionst()=default;
  virtual void help();

protected:
  virtual void get_command_line_options(optionst &options);
  virtual int do_bmc(bmct &bmc, const goto_functionst &goto_functions);
};

#endif // CPROVER_CEGIS_RUNNER_CEGIS_PARSE_OPTIONS_H

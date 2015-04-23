/*******************************************************************\

Module: mmcc Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_PARSEOPTIONS_H
#define CPROVER_CBMC_PARSEOPTIONS_H

#include <util/parse_options.h>

#include <langapi/language_ui.h>

#define MMCC_OPTIONS \
  ""

class mmcc_parse_optionst:public parse_options_baset
{
public:
  virtual int doit();
  virtual void help();

  mmcc_parse_optionst(int argc, const char **argv);

protected:
  int convert(std::istream &, const std::string &);
};

#endif

/*******************************************************************\

Module: A special command line object for the gcc-like options

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// A special command line object for the gcc-like options

#ifndef CPROVER_GOTO_CC_GCC_CMDLINE_H
#define CPROVER_GOTO_CC_GCC_CMDLINE_H

#include "goto_cc_cmdline.h"

class gcc_cmdlinet:public goto_cc_cmdlinet
{
public:
  // overload
  virtual bool parse(int, const char**);

  gcc_cmdlinet()
  {
  }

protected:
  using argst = std::vector<std::string>;

  bool parse_arguments(const argst &args, bool in_spec_file);
  void parse_specs();
  void parse_specs_line(const std::string &line);
};

#endif // CPROVER_GOTO_CC_GCC_CMDLINE_H

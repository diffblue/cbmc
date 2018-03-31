/*******************************************************************\

Module: A special command line object for the ld-like options

Author: Daniel Kroening

Date: Feb 2013

\*******************************************************************/

/// \file
/// A special command line object for the ld-like options

#ifndef CPROVER_GOTO_CC_LD_CMDLINE_H
#define CPROVER_GOTO_CC_LD_CMDLINE_H

#include "goto_cc_cmdline.h"

class ld_cmdlinet:public goto_cc_cmdlinet
{
public:
  // overload
  virtual bool parse(int, const char**);

  ld_cmdlinet()
  {
  }
};

#endif // CPROVER_GOTO_CC_LD_CMDLINE_H

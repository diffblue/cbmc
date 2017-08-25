/*******************************************************************\

Module: A special command line object to mimic ARM's armcc

Author: Daniel Kroening

Date: June 2006

\*******************************************************************/

/// \file
/// A special command line object to mimic ARM's armcc

#ifndef CPROVER_GOTO_CC_ARMCC_CMDLINE_H
#define CPROVER_GOTO_CC_ARMCC_CMDLINE_H

#include "goto_cc_cmdline.h"

class armcc_cmdlinet:public goto_cc_cmdlinet
{
public:
  virtual bool parse(int, const char**);

  armcc_cmdlinet()
  {
  }
};

#endif // CPROVER_GOTO_CC_ARMCC_CMDLINE_H

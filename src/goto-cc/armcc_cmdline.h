/*******************************************************************\
 
Module: A special command line object to mimick ARM's armcc
 
Author: Daniel Kroening
 
Date: June 2006
 
\*******************************************************************/

#ifndef GOTO_CC_ARMCC_CMDLINE_H
#define GOTO_CC_ARMCC_CMDLINE_H

#include "goto_cc_cmdline.h"

class armcc_cmdlinet:public goto_cc_cmdlinet
{
public:
  virtual bool parse(int, const char**);

  armcc_cmdlinet()
  {
  }
};

#endif /* GOTO_CC_ARMCC_CMDLINE_H */

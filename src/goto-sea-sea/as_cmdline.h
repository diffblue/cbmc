/*******************************************************************\
 
Module: A special command line object for GNU Assembler
 
Author: Michael Tautschnig
 
Date: July 2016
 
\*******************************************************************/

/// \file
///  A special command line object for GNU Assembler Author: Michael Tautschnig
///   Date: July 2016

#ifndef CPROVER_GOTO_CC_AS_CMDLINE_H
#define CPROVER_GOTO_CC_AS_CMDLINE_H

#include "goto_cc_cmdline.h"

class as_cmdlinet:public goto_cc_cmdlinet
{
public:
  // overload
  virtual bool parse(int, const char**);

  as_cmdlinet()
  {
  }
};

#endif // CPROVER_GOTO_CC_AS_CMDLINE_H

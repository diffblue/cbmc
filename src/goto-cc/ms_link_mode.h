/*******************************************************************\

Module: Visual Studio Link Mode

Author: Daniel Kroening

Date: July 2018

\*******************************************************************/

/// \file
/// Visual Studio Link Mode

#ifndef CPROVER_GOTO_CC_MS_LINK_MODE_H
#define CPROVER_GOTO_CC_MS_LINK_MODE_H

#include "cl_message_handler.h"
#include "compile.h"
#include "goto_cc_mode.h"

class ms_link_modet : public goto_cc_modet
{
public:
  int doit() final;
  void help_mode() final;

  explicit ms_link_modet(goto_cc_cmdlinet &);

protected:
  cl_message_handlert message_handler;
};

#endif // CPROVER_GOTO_CC_MS_LINK_MODE_H

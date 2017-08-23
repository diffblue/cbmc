/*******************************************************************\

Module: Command line interpretation for goto-cc.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Command line interpretation for goto-cc.

#ifndef CPROVER_GOTO_CC_GOTO_CC_MODE_H
#define CPROVER_GOTO_CC_GOTO_CC_MODE_H

#include "goto_cc_cmdline.h"

#include <util/message.h>

class goto_cc_modet:public messaget
{
public:
  virtual int main(int argc, const char **argv);
  virtual int doit()=0;
  virtual void help_mode()=0;
  virtual void help();
  virtual void usage_error();

  goto_cc_modet(
    goto_cc_cmdlinet &,
    const std::string &_base_name,
    message_handlert &);
  ~goto_cc_modet();

protected:
  goto_cc_cmdlinet &cmdline;
  const std::string base_name;
  void register_languages();
};

#endif // CPROVER_GOTO_CC_GOTO_CC_MODE_H

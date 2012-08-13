/*******************************************************************\

Module: Command line interpretation for goto-cc.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_MODE_H
#define GOTO_CC_MODE_H

#include <langapi/language_ui.h>

#include "goto_cc_cmdline.h"

class goto_cc_modet:public language_uit
{
public:
  std::string base_name;

  virtual int main(int argc, const char **argv);
  virtual bool doit()=0;
  virtual void help_mode()=0;
  virtual void help();
  virtual void usage_error();

  explicit goto_cc_modet(goto_cc_cmdlinet &_cmdline);
  
private:
  void register_languages();
  goto_cc_cmdlinet &cmdline;
};

#endif /* GOTO_CC_MODE_H */

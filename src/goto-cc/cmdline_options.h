/*******************************************************************\

Module: Command line interpretation for goto-cc.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_CMDLINE_OPTIONS_H
#define GOTO_CC_CMDLINE_OPTIONS_H

#include <config.h>
#include <langapi/language_ui.h>

#include "goto_cc_cmdline.h"

class cmdline_optionst:public language_uit
{
public:
  goto_cc_cmdlinet &cmdline;
  std::string my_name;

  virtual int main(int argc, const char **argv);
  virtual bool doit();
  virtual void help();
  virtual void usage_error();

  cmdline_optionst(goto_cc_cmdlinet &_cmdline);
  
private:
  void register_languages();
};

#endif /*CMDLINE_H_*/

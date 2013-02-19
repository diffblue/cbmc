/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_LD_MODE_H
#define GOTO_CC_LD_MODE_H

#include "goto_cc_mode.h"
#include "ld_cmdline.h"

class ld_modet:public goto_cc_modet
{
public:
  virtual bool doit();
  virtual void help_mode();

  explicit ld_modet(ld_cmdlinet &_ld_cmdline):
    goto_cc_modet(_ld_cmdline),
    produce_hybrid_binary(false),
    cmdline(_ld_cmdline)
  {
  }

  bool produce_hybrid_binary;
  
protected:
  ld_cmdlinet &cmdline;
  
  //int gcc_hybrid_binary(const cmdlinet::argst &input_files);
  //static bool is_supported_source_file(const std::string &);
};

#endif /* GOTO_CC_LD_MODE_H */

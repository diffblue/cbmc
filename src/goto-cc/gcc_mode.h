/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_GCC_MODE_H
#define GOTO_CC_GCC_MODE_H

#include "goto_cc_mode.h"
#include "gcc_cmdline.h"

class gcc_modet:public goto_cc_modet
{
public:
  virtual bool doit();
  virtual void help_mode();

  explicit gcc_modet(gcc_cmdlinet &_gcc_cmdline):
    goto_cc_modet(_gcc_cmdline),
    produce_hybrid_binary(false),
    cmdline(_gcc_cmdline),
    act_as_ld(false)
  {
  }

  bool produce_hybrid_binary;
  
protected:
  gcc_cmdlinet &cmdline;
  
  bool act_as_ld;
  
  int preprocess(const std::string &src, const std::string &dest);
  
  int gcc_hybrid_binary(const cmdlinet::argst &input_files);
  
  static bool is_supported_source_file(const std::string &);
};

#endif /* GOTO_CC_GCC_MODE_H */

/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_GCC_MODE_H
#define CPROVER_GOTO_CC_GCC_MODE_H

#include "goto_cc_mode.h"

class gcc_modet:public goto_cc_modet
{
public:
  virtual int doit();
  virtual void help_mode();

  gcc_modet(
    goto_cc_cmdlinet &_cmdline,
    const std::string &_base_name,
    bool _produce_hybrid_binary);

protected:
  const bool produce_hybrid_binary;

  const bool act_as_ld;
  std::string native_tool_name;

  int preprocess(
    const std::string &language,
    const std::string &src,
    const std::string &dest);

  int run_gcc(); // call gcc with original command line

  int gcc_hybrid_binary();

  static bool needs_preprocessing(const std::string &);
};

#endif // CPROVER_GOTO_CC_GCC_MODE_H

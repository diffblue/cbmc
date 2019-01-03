/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Base class for command line interpretation

#ifndef CPROVER_GOTO_CC_GCC_MODE_H
#define CPROVER_GOTO_CC_GCC_MODE_H

#include "compile.h"
#include "gcc_message_handler.h"
#include "gcc_version.h"
#include "goto_cc_mode.h"

#include <set>

class gcc_modet:public goto_cc_modet
{
public:
  int doit() final;
  void help_mode() final;

  gcc_modet(
    goto_cc_cmdlinet &_cmdline,
    const std::string &_base_name,
    bool _produce_hybrid_binary);

protected:
  gcc_message_handlert gcc_message_handler;

  const bool produce_hybrid_binary;

  std::string native_tool_name;

  const std::string goto_binary_tmp_suffix;

  /// \brief Associate CBMC architectures with processor names
  const std::map<std::string, std::set<std::string>> arch_map;

  int preprocess(
    const std::string &language,
    const std::string &src,
    const std::string &dest,
    bool act_as_bcc);

  /// \brief call gcc with original command line
  int run_gcc(const compilet &compiler);

  int gcc_hybrid_binary(compilet &compiler);

  int asm_output(
    bool act_as_bcc,
    const std::list<std::string> &preprocessed_source_files,
    const compilet &compiler);

  static bool needs_preprocessing(const std::string &);

  gcc_versiont gcc_version;
};

#endif // CPROVER_GOTO_CC_GCC_MODE_H

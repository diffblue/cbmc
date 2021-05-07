/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Base class for command line interpretation

#ifndef CPROVER_GOTO_CC_LD_MODE_H
#define CPROVER_GOTO_CC_LD_MODE_H

#include "gcc_message_handler.h"
#include "goto_cc_mode.h"

class ld_modet : public goto_cc_modet
{
public:
  int doit() final;
  void help_mode() final;

  ld_modet(
    goto_cc_cmdlinet &_cmdline,
    const std::string &_base_name);

protected:
  gcc_message_handlert gcc_message_handler;

  std::string native_tool_name;

  const std::string goto_binary_tmp_suffix;

  /// \brief call ld with original command line
  int run_ld();

  /// Build an ELF or Mach-O binary containing a goto-cc section.
  /// \param building_executable: set to true iff the target file is an
  ///   executable
  /// \param object_files: object files to be linked
  /// \return zero, unless an error occurred
  int ld_hybrid_binary(
    bool building_executable,
    const std::list<std::string> &object_files);
};

#endif // CPROVER_GOTO_CC_LD_MODE_H

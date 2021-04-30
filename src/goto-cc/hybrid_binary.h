/*******************************************************************\

Module: Create hybrid binary with goto-binary section

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

/// \file
/// Create hybrid binary with goto-binary section

#ifndef CPROVER_GOTO_CC_HYBRID_BINARY_H
#define CPROVER_GOTO_CC_HYBRID_BINARY_H

#include <string>

class message_handlert;

/// \brief Merges a goto binary into an object file (e.g. ELF)
/// \param compiler_or_linker: The name of the gcc or ld executable, used to
///   deduce the name of objcopy
/// \param goto_binary_file: The file name of the goto binary
/// \param output_file: The name of the object file; the result is stored here.
/// \param building_executable: The \p output_file is an executable.
/// \param message_handler: Message handler for output.
/// \param linking_efi: Set to true if linking x86 EFI binaries to relax error
///   checking.
int hybrid_binary(
  const std::string &compiler_or_linker,
  const std::string &goto_binary_file,
  const std::string &output_file,
  bool building_executable,
  message_handlert &message_handler,
  bool linking_efi = false);

/// Return the name of the objcopy tool matching the chosen compiler or linker
/// command.
/// \param compiler_or_linker: Compiler or linker commmand
std::string objcopy_command(const std::string &compiler_or_linker);

#endif // CPROVER_GOTO_CC_HYBRID_BINARY_H

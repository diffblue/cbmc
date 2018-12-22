/*******************************************************************\

Module: Create hybrid binary with goto-binary section

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

/// \file
/// Create hybrid binary with goto-binary section

#ifndef CPROVER_GOTO_CC_HYBRID_BINARY_H
#define CPROVER_GOTO_CC_HYBRID_BINARY_H

#include <util/message.h>

#include <string>

/// \brief Merges a goto binary into an object file (e.g. ELF)
/// \param compiler_or_linker: The name of the gcc or ld executable,
///        used to deduce the name of objcopy
/// \param goto_binary_file: The file name of the goto binary
/// \param output_file: The name of the object file; the result is
///        stored here.
int hybrid_binary(
  const std::string &compiler_or_linker,
  const std::string &goto_binary_file,
  const std::string &output_file,
  message_handlert &);

#endif // CPROVER_GOTO_CC_HYBRID_BINARY_H

/*******************************************************************\

Module: Read Goto Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Read Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
#define CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H

#include <list>
#include <string>

#include <util/optional.h>

class goto_modelt;
class message_handlert;

optionalt<goto_modelt>
read_goto_binary(const std::string &filename, message_handlert &);

bool is_goto_binary(const std::string &filename, message_handlert &);

/// Reads object files and updates the config if any files were read.
/// \param file_names: file names of goto binaries; if empty, just returns false
/// \param dest: goto model to update
/// \param message_handler: for diagnostics
/// \return True on error, false otherwise
bool read_objects_and_link(
  const std::list<std::string> &file_names,
  goto_modelt &dest,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H

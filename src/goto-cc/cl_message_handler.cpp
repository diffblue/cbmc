/*******************************************************************\

Module: Print messages like CL.exe does

Author: Michael Tautschnig

\*******************************************************************/

#include "cl_message_handler.h"

#include <util/unicode.h>

#include <fstream>
#include <iostream>
#include <sstream>

void cl_message_handlert::print(
  unsigned level,
  const std::string &message,
  const source_locationt &location)
{
  if(verbosity < level || location == source_locationt())
  {
    console_message_handlert::print(level, message);
    return;
  }

  std::ostringstream formatted_message;

  const irep_idt file = location.get_file();
  const std::string &line = id2string(location.get_line());
  formatted_message << file << '(' << line << "): ";

  if(level == messaget::M_ERROR)
    formatted_message << "error: ";
  else if(level == messaget::M_WARNING)
    formatted_message << "warning: ";

  formatted_message << message;

  const auto full_path = location.full_path();

  if(full_path.has_value() && !line.empty())
  {
#ifdef _WIN32
    std::ifstream in(widen(full_path.value()));
#else
    std::ifstream in(full_path.value());
#endif
    if(in)
    {
      const auto line_number = std::stoull(line);
      std::string source_line;
      for(std::size_t l = 0; l < line_number; l++)
        std::getline(in, source_line);

      if(in)
      {
        formatted_message << '\n';
        formatted_message << file << '(' << line << "): " << source_line;
      }
    }
  }

  console_message_handlert::print(level, formatted_message.str());
}

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "gcc_message_handler.h"

#include <util/unicode.h>

#include <fstream>
#include <iostream>

void gcc_message_handlert::print(
  unsigned level,
  const std::string &message,
  const source_locationt &location)
{
  message_handlert::print(level, message);

  if(verbosity >= level)
  {
    // gcc appears to send everything to cerr
    auto &out = std::cerr;

    const irep_idt file = location.get_file();
    const irep_idt line = location.get_line();
    const irep_idt column = location.get_column();
    const irep_idt function = location.get_function();

    if(!function.empty())
    {
      if(!file.empty())
        out << string(messaget::bold) << file << ':' << string(messaget::reset)
            << ' ';
      out << "In function " << string(messaget::bold) << '\'' << function
          << '\'' << string(messaget::reset) << ":\n";
    }

    if(!line.empty())
    {
      out << string(messaget::bold);

      if(!file.empty())
        out << file << ':';

      out << line << ':';

      if(column.empty())
        out << "1: ";
      else
        out << column << ": ";

      if(level == messaget::M_ERROR)
        out << string(messaget::red) << "error: ";
      else if(level == messaget::M_WARNING)
        out << string(messaget::bright_magenta) << "warning: ";

      out << string(messaget::reset);
    }

    out << message << '\n';

    const auto file_name = location.full_path();
    if(file_name.has_value() && !line.empty())
    {
#ifdef _WIN32
      std::ifstream in(widen(file_name.value()));
#else
      std::ifstream in(file_name.value());
#endif
      if(in)
      {
        const auto line_number = std::stoull(id2string(line));
        std::string source_line;
        for(std::size_t l = 0; l < line_number; l++)
          std::getline(in, source_line);

        if(in)
          out << ' ' << source_line << '\n'; // gcc adds a space, clang doesn't
      }
    }

    out << std::flush;
  }
}

void gcc_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  message_handlert::print(level, message);

  // gcc appears to send everything to cerr
  if(verbosity>=level)
    std::cerr << message << '\n' << std::flush;
}

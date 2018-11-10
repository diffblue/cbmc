/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cout_message.h"

#include <fstream>
#include <iostream>

#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include <cstdio>
#include <util/pragma_pop.def>
#else
#include <unistd.h>
#endif

#include "unicode.h"

cout_message_handlert::cout_message_handlert():
  stream_message_handlert(std::cout)
{
}

cerr_message_handlert::cerr_message_handlert():
  stream_message_handlert(std::cerr)
{
}

console_message_handlert::console_message_handlert(bool _always_flush)
  : always_flush(_always_flush), is_a_tty(false), use_SGR(false)
{
#ifdef _WIN32
  HANDLE out_handle=GetStdHandle(STD_OUTPUT_HANDLE);

  DWORD consoleMode;
  if(GetConsoleMode(out_handle, &consoleMode))
  {
    is_a_tty = true;

#ifdef ENABLE_VIRTUAL_TERMINAL_PROCESSING
    consoleMode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
    if(SetConsoleMode(out_handle, consoleMode))
      use_SGR = true;
#endif
  }
#else
  is_a_tty = isatty(STDOUT_FILENO);
  use_SGR = is_a_tty;
#endif
}

/// Create an ECMA-48 SGR (Select Graphic Rendition) command with
/// given code.
/// \param c: ECMA-48 command code
std::string console_message_handlert::command(unsigned c) const
{
  if(!use_SGR)
    return std::string();

  return "\x1b[" + std::to_string(c) + 'm';
}

void console_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  message_handlert::print(level, message);

  if(verbosity<level)
    return;

  #ifdef _WIN32
  HANDLE out_handle=
    GetStdHandle((level>1)?STD_OUTPUT_HANDLE:STD_ERROR_HANDLE);

  // We use UTF16 when we write to the console,
  // but we write UTF8 otherwise.

  DWORD consoleMode;
  if(GetConsoleMode(out_handle, &consoleMode))
  {
    // writing to the console
    std::wstring wide_message=widen(message);

    DWORD number_written;

    WriteConsoleW(
      out_handle, wide_message.c_str(),
      (DWORD)wide_message.size(), &number_written, NULL);

    WriteConsoleW(out_handle, L"\r\n", 2, &number_written, NULL);
  }
  else
  {
    // writing to a file

    if(level>=4)
    {
      std::cout << message << '\n';
    }
    else
      std::cerr << message << '\n';
  }
  #else
  // Messages level 3 or lower go to cerr, messages level 4 or
  // above go to cout.

  if(level>=4)
  {
    std::cout << message << '\n';
  }
  else
    std::cerr << message << '\n';
  #endif
}

void console_message_handlert::flush(unsigned level)
{
  // We flush after messages of level 6 or lower.
  // We don't for messages of level 7 or higher to improve performance,
  // in particular when writing to NFS.
  if(level>=4)
  {
    if(level <= 6 || always_flush)
      std::cout << std::flush;
  }
  else
    std::cerr << std::flush;
}

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

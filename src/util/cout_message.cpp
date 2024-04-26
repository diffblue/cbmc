/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cout_message.h"

#include <iostream>

// clang-format off
// clang-format must not re-order includes here to avoid pragma_push/pragma_pop
// being moved around
#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#pragma warning(disable : 5039)
// pointer or reference to potentially throwing function passed to extern C
#endif
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include <cstdio>
#include <util/pragma_pop.def>
#include "unicode.h"
// clang-format on
#else
#include <unistd.h>
#endif

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
  // quote_begin and quote_end
  if(c == '<' || c == '>')
    return "'";

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

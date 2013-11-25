/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#ifdef _WIN32
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include <cstdio>
#endif 

#include "unicode.h"
#include "cout_message.h"

void cout_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  std::cout << message << '\n';

  // We flush for level 6 or below.
  if(level<=6) std::cout << std::flush;
}
 
void cerr_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  std::cerr << message << '\n' << std::flush;
}

void console_message_handlert::print(
  unsigned level,
  const std::string &message)
{ 
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
      wide_message.size(), &number_written, NULL);

    WriteConsoleW(out_handle, L"\r\n", 2, &number_written, NULL);
  }
  else
  {
    // writing to a file

    if(level>=4)
    {
      std::cout << message << '\n';

      if(level<=6)
        std::cout << std::flush;
    }
    else
      std::cerr << message << '\n' << std::flush;
  }
  #else
  // We flush after messages of level 6 or lower.
  // We don't for messages of level 7 or higher to improve performance,
  // in particular when writing to NFS.
  // Messages level 3 or lower go to cerr, messages level 4 or
  // above go to cout.

  if(level>=4)
  {
    std::cout << message << '\n';

    if(level<=6)
      std::cout << std::flush;
  }
  else
    std::cerr << message << '\n' << std::flush;
  #endif
}

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#ifdef _WIN32
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include <stdio.h>
#endif 

#include "unicode.h"
#include "cout_message.h"

void cout_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  std::cout << message << std::endl;
}
 
void cerr_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  std::cerr << message << std::endl;
}

void console_message_handlert::print(
  unsigned level,
  const std::string &message)
{ 
  #ifdef _WIN32
  HANDLE out_handle=
    GetStdHandle((level>1)?STD_OUTPUT_HANDLE:STD_ERROR_HANDLE);

  // We write UTF16 when we write to the console,
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
    if(level>1)
      std::cout << message << std::endl;
    else
      std::cerr << message << std::endl;
  }
  #else
  if(level>1)
    std::cout << message << std::endl;
  else
    std::cerr << message << std::endl;
  #endif
}

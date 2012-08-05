/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#ifdef _WIN32
#include <windows.h>
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
    GetStdHandle((level>1)?STD_OUTPUT_HANDLE:ERR_OUTPUT_HANDLE);

  DWORD number_written;
  std::wstring wide_message=widen(message);
  WriteConsoleW(
    out_handle, wide_messsage.c_str(),
    wide_message.size(), &number_written, NULL);
  
  #else
  if(level>1)
    std::cout << message << std::endl;
  else
    std::cerr << message << std::endl;
  #endif
}

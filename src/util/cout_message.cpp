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

/*******************************************************************\

Function: cout_message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cout_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  if(verbosity>=level)
  {
    std::cout << message << '\n';

    // We flush for level 6 or below.
    if(level<=6) std::cout << std::flush;
  }
}

/*******************************************************************\

Function: cerr_message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cerr_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  if(verbosity>=level)
    std::cerr << message << '\n' << std::flush;
}

/*******************************************************************\

Function: consolte_message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void console_message_handlert::print(
  unsigned level,
  const std::string &message)
{
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

/*******************************************************************\

Function: gcc_message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gcc_message_handlert::print(
  unsigned level,
  const std::string &message,
  int sequence_number,
  const source_locationt &location)
{
  const irep_idt file=location.get_file();
  const irep_idt line=location.get_line();
  const irep_idt column=location.get_column();
  const irep_idt function=location.get_function();
  
  std::string dest;

  if(!function.empty())
  {
    if(!file.empty())
      dest+=id2string(file)+":";
    if(dest!="") dest+=' ';
    dest+="In function '"+id2string(function)+"':\n";
  }

  if(!line.empty())
  {
    if(!file.empty())
      dest+=id2string(file)+":";

    dest+=id2string(line)+":";

    if(column.empty())
      dest+="1: ";
    else
      dest+=id2string(column)+": ";

    if(level==message_clientt::M_ERROR)
      dest+="error: ";
    else if(level==message_clientt::M_WARNING)
      dest+="warning: ";
  }

  dest+=message;

  print(level, dest);
}

/*******************************************************************\

Function: gcc_message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gcc_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  // gcc appears to send everything to cerr
  std::cerr << message << '\n' << std::flush;
}

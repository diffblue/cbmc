/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cout_message.h"

#include <iostream>

#ifdef _WIN32
#include <windows.h>
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

void console_message_handlert::setup_console()
{
#ifdef _WIN32
  // We avoid doing this more than once,
  // as setting the code page may be slow.
  static bool code_page_set = false;

  if(!code_page_set)
  {
    // We use UTF8 for unicode characters.
    // 65001 is the magic number for the UTF8 codepage.
    // https://docs.microsoft.com/en-us/windows/desktop/intl/code-page-identifiers
    SetConsoleOutputCP(65001);
    code_page_set = true;
  }
#endif
}

void console_message_handlert::print(unsigned level, const std::string &message)
{
  if(verbosity < level)
    return;

  // Messages level 3 or lower go to cerr, messages level 4 or
  // above go to cout.

  if(level>=4)
  {
    std::cout << message << '\n';
  }
  else
    std::cerr << message << '\n';
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
  const irep_idt file=location.get_file();
  const irep_idt line=location.get_line();
  const irep_idt column=location.get_column();
  const irep_idt function=location.get_function();

  std::string dest;

  if(!function.empty())
  {
    if(!file.empty())
      dest+=id2string(file)+":";
    if(dest!="")
      dest+=' ';
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

    if(level==messaget::M_ERROR)
      dest+="error: ";
    else if(level==messaget::M_WARNING)
      dest+="warning: ";
  }

  dest+=message;

  print(level, dest);
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

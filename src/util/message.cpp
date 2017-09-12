/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "message.h"

void message_handlert::print(
  unsigned level,
  const std::string &message,
  int sequence_number,
  const source_locationt &location,
  bool preformatted)
{
  std::string dest;

  const irep_idt &file=location.get_file();
  const irep_idt &line=location.get_line();
  const irep_idt &column=location.get_column();
  const irep_idt &function=location.get_function();

  if(!file.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="file "+id2string(file);
  }
  if(!line.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="line "+id2string(line);
  }
  if(!column.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="column "+id2string(column);
  }
  if(!function.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="function "+id2string(function);
  }

  if(dest!="")
    dest+=": ";
  dest+=message;

  print(level, dest, preformatted);
}

void message_handlert::print(
  unsigned level,
  const std::string &message,
  bool preformatted)
{
  if(level>=message_count.size())
    message_count.resize(level+1, 0);
  ++message_count[level];
}

messaget::~messaget()
{
}

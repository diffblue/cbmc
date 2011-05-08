/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "message.h"
#include "i2string.h"

/*******************************************************************\

Function: message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void message_handlert::print(
  unsigned level,
  const std::string &message,
  int sequence_number,
  const locationt &location)
{
  std::string dest;
  
  const irep_idt &file=location.get_file();
  const irep_idt &line=location.get_line();
  const irep_idt &column=location.get_column();
  const irep_idt &function=location.get_function();

  if(file!="")     { if(dest!="") dest+=" "; dest+="file "+id2string(file); }
  if(line!="")     { if(dest!="") dest+=" "; dest+="line "+id2string(line); }
  if(column!="")   { if(dest!="") dest+=" "; dest+="column "+id2string(column); }
  if(function!="") { if(dest!="") dest+=" "; dest+="function "+id2string(function); }

  if(dest!="") dest+=": ";
  dest+=message;

  print(level, dest);
}

/*******************************************************************\

Function: messaget::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void messaget::print(unsigned level, const std::string &message)
{
  if(message_handler!=NULL && verbosity>=level)
    message_handler->print(level, message);
}
  
/*******************************************************************\

Function: messaget::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void messaget::print(
  unsigned level,
  const std::string &message,
  int sequence_number,
  const locationt &location)
{
  if(message_handler!=NULL && verbosity>=level)
    message_handler->print(level, message, sequence_number,
                           location);
}
  
/*******************************************************************\

Function: message_clientt::set_message_handler

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void message_clientt::set_message_handler(
  message_handlert &_message_handler)
{
  message_handler=&_message_handler;
}

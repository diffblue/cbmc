/*******************************************************************\

Module: Read Goto Programs

Author:

\*******************************************************************/

#include <fstream>

#include <message.h>

#include "read_goto_binary.h"
#include "read_bin_goto_object.h"

/*******************************************************************\

Function: read_goto_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool read_goto_binary(
  const std::string &filename,
  contextt &context,
  goto_functionst &dest,
  message_handlert &message_handler)
{
  std::ifstream in(filename.c_str(), std::ios::binary);

  if(!in)
  {
    messaget message(message_handler);
    message.error(
      std::string("Failed to open `")+filename+"'");
    return true;
  }

  return read_bin_goto_object(in, filename, context, dest, message_handler);
}

/*******************************************************************\

Function: is_goto_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_goto_binary(const std::string &filename)
{
  std::ifstream in(filename.c_str(), std::ios::binary);

  if(!in) return false;

  char hdr[4];
  hdr[0]=in.get();
  hdr[1]=in.get();
  hdr[2]=in.get();    
  hdr[3]=in.get();

  if(hdr[0]==0x7f && hdr[1]=='G' && hdr[2]=='B' && hdr[3]=='F')
    return true;
  
  return false;
}

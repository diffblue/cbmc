/*******************************************************************\

Module: Read Goto Programs

Author:

\*******************************************************************/

#include <fstream>

#include <message.h>
#include <unicode.h>

#include "read_goto_binary.h"
#include "read_bin_goto_object.h"
#include "elf_reader.h"

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
  #ifdef _MSC_VER
  std::ifstream in(widen(filename).c_str(), std::ios::binary);
  #else
  std::ifstream in(filename.c_str(), std::ios::binary);
  #endif

  if(!in)
  {
    messaget message(message_handler);
    message.error(
      std::string("Failed to open `")+filename+"'");
    return true;
  }
  
  char hdr[4];
  hdr[0]=in.get();
  hdr[1]=in.get();
  hdr[2]=in.get();    
  hdr[3]=in.get();
  in.seekg(0);

  if(hdr[0]==0x7f && hdr[1]=='G' && hdr[2]=='B' && hdr[3]=='F')
  {
    return read_bin_goto_object(in, filename, context, dest, message_handler);
  }
  else if(hdr[0]==0x7f && hdr[1]=='E' && hdr[2]=='L' && hdr[3]=='F')
  {
    // this _may_ have a goto-cc section
    try
    {
      elf_readert elf_reader(in);
      
      for(unsigned i=0; i<elf_reader.number_of_sections; i++)
        if(elf_reader.section_name(i)=="goto-cc")
        {
          in.seekg(elf_reader.section_offset(i));
          return read_bin_goto_object(in, filename, context, dest, message_handler);
        }
        
      // section not found
      messaget(message_handler).error("failed to find goto-cc section in ELF binary");
    }
    
    catch(const char *s)
    {
      messaget(message_handler).error(s);
    }
  }
  else
  {
    messaget(message_handler).error("not a goto binary");
  }
  
  return true;
}

/*******************************************************************\

Function: is_goto_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_goto_binary(const std::string &filename)
{
  #ifdef _MSC_VER
  std::ifstream in(widen(filename).c_str(), std::ios::binary);
  #else
  std::ifstream in(filename.c_str(), std::ios::binary);
  #endif
  
  if(!in) return false;
  
  // We accept two forms:
  // 1. goto binaries, marked with 0x7f GBF
  // 2. ELF binaries, marked with 0x7f ELF

  char hdr[4];
  hdr[0]=in.get();
  hdr[1]=in.get();
  hdr[2]=in.get();    
  hdr[3]=in.get();

  if(hdr[0]==0x7f && hdr[1]=='G' && hdr[2]=='B' && hdr[3]=='F')
  {
    return true; // yes, this is a goto binary
  }
  else if(hdr[0]==0x7f && hdr[1]=='E' && hdr[2]=='L' && hdr[3]=='F')
  {
    // this _may_ have a goto-cc section
    try
    {
      in.seekg(0);
      elf_readert elf_reader(in);
      if(elf_reader.has_section("goto-cc")) return true;
    }
    
    catch(...)
    {
      // ignore any errors
    }
  }
  
  return false;
}

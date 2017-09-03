/*******************************************************************\

Module: Read Goto Programs

Author:

\*******************************************************************/

/// \file
/// Read Goto Programs

#include "read_goto_binary.h"

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include <fstream>
#include <unordered_set>

#include <util/message.h>
#include <util/unicode.h>
#include <util/tempfile.h>
#include <util/rename_symbol.h>
#include <util/base_type.h>
#include <util/config.h>

#include <langapi/language_ui.h>

#include "goto_model.h"
#include "link_goto_model.h"
#include "read_bin_goto_object.h"
#include "elf_reader.h"
#include "osx_fat_reader.h"

bool read_goto_binary(
  const std::string &filename,
  goto_modelt &dest,
  message_handlert &message_handler)
{
  return read_goto_binary(
    filename, dest.symbol_table, dest.goto_functions, message_handler);
}

bool read_goto_binary(
  const std::string &filename,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  #ifdef _MSC_VER
  std::ifstream in(widen(filename), std::ios::binary);
  #else
  std::ifstream in(filename, std::ios::binary);
  #endif

  if(!in)
  {
    messaget message(message_handler);
    message.error() << "Failed to open `" << filename << "'"
                    << messaget::eom;
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
    return read_bin_goto_object(
      in, filename, symbol_table, goto_functions, message_handler);
  }
  else if(hdr[0]==0x7f && hdr[1]=='E' && hdr[2]=='L' && hdr[3]=='F')
  {
    // ELF binary.
    // This _may_ have a goto-cc section.
    try
    {
      elf_readert elf_reader(in);

      for(unsigned i=0; i<elf_reader.number_of_sections; i++)
        if(elf_reader.section_name(i)=="goto-cc")
        {
          in.seekg(elf_reader.section_offset(i));
          return read_bin_goto_object(
            in, filename, symbol_table, goto_functions, message_handler);
        }

      // section not found
      messaget(message_handler).error() <<
        "failed to find goto-cc section in ELF binary" << messaget::eom;
    }

    catch(const char *s)
    {
      messaget(message_handler).error() << s << messaget::eom;
    }
  }
  else if(is_osx_fat_magic(hdr))
  {
    std::string tempname;
    // Mach-O universal binary
    // This _may_ have a goto binary as hppa7100LC architecture
    try
    {
      osx_fat_readert osx_fat_reader(in);

      if(osx_fat_reader.has_gb())
      {
        tempname=get_temporary_file("tmp.goto-binary", ".gb");
        osx_fat_reader.extract_gb(filename, tempname);

        std::ifstream temp_in(tempname, std::ios::binary);
        if(!temp_in)
          messaget(message_handler).error() << "failed to read temp binary"
                                            << messaget::eom;
        const bool read_err=read_bin_goto_object(
          temp_in, filename, symbol_table, goto_functions, message_handler);
        temp_in.close();

        unlink(tempname.c_str());
        return read_err;
      }

      // architecture not found
      messaget(message_handler).error() <<
        "failed to find goto binary in Mach-O file" << messaget::eom;
    }

    catch(const char *s)
    {
      if(!tempname.empty())
        unlink(tempname.c_str());
      messaget(message_handler).error() << s << messaget::eom;
    }
  }
  else
  {
    messaget(message_handler).error() <<
      "not a goto binary" << messaget::eom;
  }

  return true;
}

bool is_goto_binary(const std::string &filename)
{
  #ifdef _MSC_VER
  std::ifstream in(widen(filename), std::ios::binary);
  #else
  std::ifstream in(filename, std::ios::binary);
  #endif

  if(!in)
    return false;

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
      if(elf_reader.has_section("goto-cc"))
        return true;
    }

    catch(...)
    {
      // ignore any errors
    }
  }
  else if(is_osx_fat_magic(hdr))
  {
    // this _may_ have a goto binary as hppa7100LC architecture
    try
    {
      in.seekg(0);
      osx_fat_readert osx_fat_reader(in);
      if(osx_fat_reader.has_gb())
        return true;
    }

    catch(...)
    {
      // ignore any errors
    }
  }

  return false;
}

/// reads an object file
/// \par parameters: a file_name
/// \return true on error, false otherwise
bool read_object_and_link(
  const std::string &file_name,
  goto_modelt &dest,
  message_handlert &message_handler)
{
  messaget(message_handler).statistics() << "Reading: "
                                         << file_name << messaget::eom;

  // we read into a temporary model
  goto_modelt temp_model;

  if(read_goto_binary(
      file_name,
      temp_model,
      message_handler))
    return true;

  try
  {
    link_goto_model(dest, temp_model, message_handler);
  }
  catch(...)
  {
    return true;
  }

  // reading successful, let's update config
  config.set_from_symbol_table(dest.symbol_table);

  return false;
}

/// reads an object file
/// \par parameters: a file_name
/// \return true on error, false otherwise
bool read_object_and_link(
  const std::string &file_name,
  symbol_tablet &dest_symbol_table,
  goto_functionst &dest_functions,
  message_handlert &message_handler)
{
  goto_modelt goto_model;

  goto_model.symbol_table.swap(dest_symbol_table);
  goto_model.goto_functions.swap(dest_functions);

  bool result=read_object_and_link(
    file_name,
    goto_model,
    message_handler);

  goto_model.symbol_table.swap(dest_symbol_table);
  goto_model.goto_functions.swap(dest_functions);

  return result;
}

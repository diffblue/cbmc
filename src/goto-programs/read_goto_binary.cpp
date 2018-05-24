/*******************************************************************\

Module: Read Goto Programs

Author:

\*******************************************************************/

/// \file
/// Read Goto Programs

#include "read_goto_binary.h"

#include <fstream>

#include <util/config.h>
#include <util/message.h>
#include <util/tempfile.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include "goto_model.h"
#include "link_goto_model.h"
#include "read_bin_goto_object.h"
#include "elf_reader.h"
#include "osx_fat_reader.h"

static bool read_goto_binary(
  const std::string &filename,
  symbol_tablet &,
  goto_functionst &,
  message_handlert &);

/// \brief Read a goto binary from a file, but do not update \ref config
/// \param filename: the file name of the goto binary
/// \param message_handler: for diagnostics
/// \return goto model on success, {} on failure
optionalt<goto_modelt>
read_goto_binary(const std::string &filename, message_handlert &message_handler)
{
  goto_modelt dest;

  if(read_goto_binary(
       filename, dest.symbol_table, dest.goto_functions, message_handler))
  {
    return {};
  }
  else
    return std::move(dest);
}

/// \brief Read a goto binary from a file, but do not update \ref config
/// \param filename: the file name of the goto binary
/// \param symbol_table: the symbol table from the goto binary
/// \param goto_functions: the goto functions from the goto binary
/// \param message_handler: for diagnostics
/// \return true on failure, false on success
static bool read_goto_binary(
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

  messaget message(message_handler);

  if(!in)
  {
    message.error() << "Failed to open '" << filename << "'" << messaget::eom;
    return true;
  }

  char hdr[8];
  in.read(hdr, 8);
  if(!in)
  {
    message.error() << "Failed to read header from '" << filename << "'"
                    << messaget::eom;
    return true;
  }

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
  else if(is_osx_fat_header(hdr))
  {
    messaget message(message_handler);

    // Mach-O universal binary
    // This _may_ have a goto binary as hppa7100LC architecture
    osx_fat_readert osx_fat_reader(in, message_handler);

    if(osx_fat_reader.has_gb())
    {
      temporary_filet tempname("tmp.goto-binary", ".gb");
      if(osx_fat_reader.extract_gb(filename, tempname()))
      {
        message.error() << "failed to extract goto binary" << messaget::eom;
        return true;
      }

      std::ifstream temp_in(tempname(), std::ios::binary);
      if(!temp_in)
        message.error() << "failed to read temp binary" << messaget::eom;

      const bool read_err = read_bin_goto_object(
        temp_in, filename, symbol_table, goto_functions, message_handler);
      temp_in.close();

      return read_err;
    }

    // architecture not found
    message.error() << "failed to find goto binary in Mach-O file"
                    << messaget::eom;
  }
  else if(is_osx_mach_object(hdr))
  {
    messaget message(message_handler);

    // Mach-O object file, may contain a goto-cc section
    try
    {
      osx_mach_o_readert mach_o_reader(in, message_handler);

      osx_mach_o_readert::sectionst::const_iterator entry =
        mach_o_reader.sections.find("goto-cc");
      if(entry != mach_o_reader.sections.end())
      {
        in.seekg(entry->second.offset);
        return read_bin_goto_object(
          in, filename, symbol_table, goto_functions, message_handler);
      }

      // section not found
      messaget(message_handler).error()
        << "failed to find goto-cc section in Mach-O binary" << messaget::eom;
    }

    catch(const deserialization_exceptiont &e)
    {
      messaget(message_handler).error() << e.what() << messaget::eom;
    }
  }
  else
  {
    messaget(message_handler).error() <<
      "not a goto binary" << messaget::eom;
  }

  return true;
}

bool is_goto_binary(
  const std::string &filename,
  message_handlert &message_handler)
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

  char hdr[8];
  in.read(hdr, 8);
  if(!in)
    return false;

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
  else if(is_osx_fat_header(hdr))
  {
    // this _may_ have a goto binary as hppa7100LC architecture
    try
    {
      in.seekg(0);
      osx_fat_readert osx_fat_reader(in, message_handler);
      if(osx_fat_reader.has_gb())
        return true;
    }

    catch(...)
    {
      // ignore any errors
    }
  }
  else if(is_osx_mach_object(hdr))
  {
    // this _may_ have a goto-cc section
    try
    {
      in.seekg(0);
      osx_mach_o_readert mach_o_reader(in, message_handler);
      if(mach_o_reader.has_section("goto-cc"))
        return true;
    }

    catch(...)
    {
      // ignore any errors
    }
  }

  return false;
}

/// \brief reads an object file, and also updates config
/// \param file_name: file name of the goto binary
/// \param dest: the goto model returned
/// \param message_handler: for diagnostics
/// \return true on error, false otherwise
static bool read_object_and_link(
  const std::string &file_name,
  goto_modelt &dest,
  message_handlert &message_handler)
{
  messaget(message_handler).status()
    << "Reading GOTO program from file " << file_name << messaget::eom;

  // we read into a temporary model
  auto temp_model = read_goto_binary(file_name, message_handler);
  if(!temp_model.has_value())
    return true;

  try
  {
    link_goto_model(dest, *temp_model, message_handler);
  }
  catch(...)
  {
    return true;
  }

  return false;
}

bool read_objects_and_link(
  const std::list<std::string> &file_names,
  goto_modelt &dest,
  message_handlert &message_handler)
{
  if(file_names.empty())
    return false;

  for(const auto &file_name : file_names)
  {
    const bool failed = read_object_and_link(file_name, dest, message_handler);

    if(failed)
      return true;
  }

  // reading successful, let's update config
  config.set_from_symbol_table(dest.symbol_table);

  return false;
}

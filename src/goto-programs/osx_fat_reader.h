/*******************************************************************\

Module: Read OS X Fat Binaries

Author:

\*******************************************************************/

/// \file
/// Read OS X Fat Binaries

#ifndef CPROVER_GOTO_PROGRAMS_OSX_FAT_READER_H
#define CPROVER_GOTO_PROGRAMS_OSX_FAT_READER_H

#include <util/message.h>

#include <fstream>
#include <map>
#include <string>

// we follow
// https://developer.apple.com/library/mac/#documentation/DeveloperTools/Conceptual/MachORuntime/Reference/reference.html

class osx_fat_readert
{
public:
  osx_fat_readert(std::ifstream &, message_handlert &);

  bool has_gb() const { return has_gb_arch; }

  bool extract_gb(
    const std::string &source,
    const std::string &dest) const;

private:
  messaget log;
  bool has_gb_arch;
};

bool is_osx_fat_header(char hdr[8]);

class osx_mach_o_readert
{
public:
  osx_mach_o_readert(std::istream &, message_handlert &);

  struct sectiont
  {
    sectiont(const std::string &_name, std::size_t _offset, std::size_t _size)
      : name(_name), offset(_offset), size(_size)
    {
    }

    std::string name;
    std::size_t offset;
    std::size_t size;
  };

  using sectionst = std::map<std::string, sectiont>;
  sectionst sections;

  bool has_section(const std::string &name) const
  {
    return sections.find(name) != sections.end();
  }

private:
  messaget log;
  std::istream &in;

  void process_commands(uint32_t ncmds, std::size_t offset, bool need_swap);

  void process_sections_32(uint32_t nsects, bool need_swap);
  void process_sections_64(uint32_t nsects, bool need_swap);
};

bool is_osx_mach_object(char hdr[8]);

#endif // CPROVER_GOTO_PROGRAMS_OSX_FAT_READER_H

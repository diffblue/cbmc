/*******************************************************************\

Module: Read ELF

Author:

\*******************************************************************/

/// \file
/// Read ELF

#include "elf_reader.h"
#include <util/exception_utils.h>

#include <istream>

elf_readert::elf_readert(std::istream &_in):in(_in)
{
  // read 32-bit header
  in.read(
    reinterpret_cast<char*>(&elf32_header),
    sizeof(elf32_header));

  if(!in)
    throw deserialization_exceptiont("failed to read ELF header");

  if(elf32_header.e_ident[0]!=0x7f ||
     elf32_header.e_ident[1]!='E' ||
     elf32_header.e_ident[2]!='L' ||
     elf32_header.e_ident[3]!='F')
    throw deserialization_exceptiont("ELF header malformed (magic)");

  elf_class=(elf_classt)elf32_header.e_ident[4];

  if(elf_class==ELF32)
  {
    const auto ei_data = elf32_header.e_ident[5];

    if(ei_data==1)
      little_endian=true;
    else if(ei_data==2)
      little_endian=false;
    else
      throw deserialization_exceptiont("ELF32 header malformed (EI_DATA)");

    if(elf32_header.e_version!=1)
      throw deserialization_exceptiont("unknown ELF32 version");

    // get offset for section header
    if(elf32_header.e_shoff==0 ||
       elf32_header.e_shnum==0)
      throw deserialization_exceptiont("ELF32 without section header");

    elf32_section_header_table.resize(elf32_header.e_shnum);
    number_of_sections=elf32_header.e_shnum;

    // iterate over these
    for(std::size_t i=0; i<elf32_section_header_table.size(); i++)
    {
      // go to right place
      in.seekg(elf32_header.e_shoff+i*elf32_header.e_shentsize);

      // read section header
      in.read(
        reinterpret_cast<char*>(&elf32_section_header_table[i]),
        sizeof(Elf32_Shdr));
    }

    // string table
    unsigned string_table_nr=elf32_header.e_shstrndx;
    if(string_table_nr>=elf32_section_header_table.size())
      throw deserialization_exceptiont("ELF32 without string table");

    string_table_offset=section_offset(string_table_nr);
  }
  else if(elf_class==ELF64)
  {
    // read 64-bit header
    in.seekg(0);
    in.read(
      reinterpret_cast<char*>(&elf64_header),
      sizeof(elf64_header));

    const auto ei_data = elf64_header.e_ident[5];

    if(ei_data==1)
      little_endian=true;
    else if(ei_data==2)
      little_endian=false;
    else
      throw deserialization_exceptiont("ELF64 header malformed (EI_DATA)");

    if(elf64_header.e_version!=1)
      throw deserialization_exceptiont("unknown ELF64 version");

    // get offset for section header
    if(elf64_header.e_shoff==0 ||
       elf64_header.e_shnum==0)
      throw deserialization_exceptiont("ELF64 without section header");

    elf64_section_header_table.resize(elf64_header.e_shnum);
    number_of_sections=elf64_header.e_shnum;

    // iterate over these
    for(std::size_t i=0; i<elf64_section_header_table.size(); i++)
    {
      // go to right place
      in.seekg(elf64_header.e_shoff+i*elf64_header.e_shentsize);

      // read section header
      in.read(
        reinterpret_cast<char*>(&elf64_section_header_table[i]),
        sizeof(Elf64_Shdr));
    }

    // string table
    unsigned string_table_nr=elf64_header.e_shstrndx;
    if(string_table_nr>=elf64_section_header_table.size())
      throw deserialization_exceptiont("ELF64 without string table");

    string_table_offset=section_offset(string_table_nr);
  }
}

std::string elf_readert::get_string(std::streampos index) const
{
  in.seekg(string_table_offset+index);

  std::string result;

  while(in)
  {
    char ch;
    in.read(&ch, 1);
    if(ch==0)
      break;
    result+=ch;
  }

  return result;
}

bool elf_readert::has_section(const std::string &name) const
{
  for(std::size_t i=0; i<number_of_sections; i++)
    if(section_name(i)==name)
      return true;

  return false;
}

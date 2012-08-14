/*******************************************************************\

Module: Read ELF

Author:

\*******************************************************************/

#ifndef CPROVER_ELF_READER_H
#define CPROVER_ELF_READER_H

#include <iostream>
#include <string>
#include <vector>

// we follow
// http://www.skyfree.org/linux/references/ELF_Format.pdf

typedef unsigned short Elf32_Half;
typedef unsigned int Elf32_Word;
typedef unsigned int Elf32_Off;
typedef unsigned int Elf32_Addr;

#define EI_NIDENT 16

typedef struct {
  unsigned char e_ident[EI_NIDENT];
  Elf32_Half e_type;
  Elf32_Half e_machine;
  Elf32_Word e_version;
  Elf32_Addr e_entry;
  Elf32_Off e_phoff;
  Elf32_Off e_shoff;
  Elf32_Word e_flags;
  Elf32_Half e_ehsize;
  Elf32_Half e_phentsize;
  Elf32_Half e_phnum;
  Elf32_Half e_shentsize;
  Elf32_Half e_shnum;
  Elf32_Half e_shstrndx;
} Elf32_Ehdr;

typedef struct {
  Elf32_Word sh_name;
  Elf32_Word sh_type;
  Elf32_Word sh_flags;
  Elf32_Addr sh_addr;
  Elf32_Off sh_offset;
  Elf32_Word sh_size;
  Elf32_Word sh_link;
  Elf32_Word sh_info;
  Elf32_Word sh_addralign;
  Elf32_Word sh_entsize;
} Elf32_Shdr;

class elf_readert
{
public:
  explicit elf_readert(std::istream &_in);
  
  // the ELF header
  Elf32_Ehdr elf_header;
  
  bool little_endian;

  // section header table  
  typedef std::vector<Elf32_Shdr> section_header_tablet;
  section_header_tablet section_header_table;

  // string table
  Elf32_Off string_table_offset;
  std::string get_string(unsigned index);

  std::string section_name(unsigned index)
  {
    return get_string(section_header_table[index].sh_name);
  }

protected:
  std::istream &in;
};

#endif

/*******************************************************************\

Module: Read ELF

Author:

\*******************************************************************/

/// \file
/// Read ELF

#ifndef CPROVER_GOTO_PROGRAMS_ELF_READER_H
#define CPROVER_GOTO_PROGRAMS_ELF_READER_H

#include <iosfwd>
#include <string>
#include <vector>

// we follow
// http://www.skyfree.org/linux/references/ELF_Format.pdf
// http://downloads.openwatcom.org/ftp/devel/docs/elf-64-gen.pdf

using Elf32_Half = unsigned short; // 2  NOLINT(readability/identifiers)
using Elf32_Word = unsigned int; // 4  NOLINT(readability/identifiers)
using Elf32_Off = unsigned int; // 4  NOLINT(readability/identifiers)
using Elf32_Addr = unsigned int; // 4  NOLINT(readability/identifiers)

using Elf64_Half = unsigned short; // 2  NOLINT(readability/identifiers)
using Elf64_Word = unsigned int; // 4  NOLINT(readability/identifiers)
using Elf64_Xword = unsigned long long int; // 8 NOLINT(readability/identifiers)
using Elf64_Off = unsigned long long int; // 8  NOLINT(readability/identifiers)
using Elf64_Addr = unsigned long long int; // 8  NOLINT(readability/identifiers)

#define EI_NIDENT 16

struct Elf32_Ehdr
{
  unsigned char e_ident[EI_NIDENT]; /* Magic number and other info */
  Elf32_Half    e_type;             /* Object file type */
  Elf32_Half    e_machine;          /* Architecture */
  Elf32_Word    e_version;          /* Object file version */
  Elf32_Addr    e_entry;            /* Entry point virtual address */
  Elf32_Off     e_phoff;            /* Program header table file offset */
  Elf32_Off     e_shoff;            /* Section header table file offset */
  Elf32_Word    e_flags;            /* Processor-specific flags */
  Elf32_Half    e_ehsize;           /* ELF header size in bytes */
  Elf32_Half    e_phentsize;        /* Program header table entry size */
  Elf32_Half    e_phnum;            /* Program header table entry count */
  Elf32_Half    e_shentsize;        /* Section header table entry size */
  Elf32_Half    e_shnum;            /* Section header table entry count */
  Elf32_Half    e_shstrndx;         /* Section header string table index */
};

struct Elf64_Ehdr
{
  unsigned char e_ident[16];        /* ELF identification */
  Elf64_Half    e_type;             /* Object file type */
  Elf64_Half    e_machine;          /* Machine type */
  Elf64_Word    e_version;          /* Object file version */
  Elf64_Addr    e_entry;            /* Entry point address */
  Elf64_Off     e_phoff;            /* Program header offset */
  Elf64_Off     e_shoff;            /* Section header offset */
  Elf64_Word    e_flags;            /* Processor-specific flags */
  Elf64_Half    e_ehsize;           /* ELF header size */
  Elf64_Half    e_phentsize;        /* Size of program header entry */
  Elf64_Half    e_phnum;            /* Number of program header entries */
  Elf64_Half    e_shentsize;        /* Size of section header entry */
  Elf64_Half    e_shnum;            /* Number of section header entries */
  Elf64_Half    e_shstrndx;         /* Section name string table index */
};

struct Elf32_Shdr
{
  Elf32_Word    sh_name;            /* Section name (string tbl index) */
  Elf32_Word    sh_type;            /* Section type */
  Elf32_Word    sh_flags;           /* Section flags */
  Elf32_Addr    sh_addr;            /* Section virtual addr at execution */
  Elf32_Off     sh_offset;          /* Section file offset */
  Elf32_Word    sh_size;            /* Section size in bytes */
  Elf32_Word    sh_link;            /* Link to another section */
  Elf32_Word    sh_info;            /* Additional section information */
  Elf32_Word    sh_addralign;       /* Section alignment */
  Elf32_Word    sh_entsize;         /* Entry size if section holds table */
};

struct Elf64_Shdr
{
  Elf64_Word    sh_name;            /* Section name */
  Elf64_Word    sh_type;            /* Section type */
  Elf64_Xword   sh_flags;           /* Section attributes */
  Elf64_Addr    sh_addr;            /* Virtual address in memory */
  Elf64_Off     sh_offset;          /* Offset in file */
  Elf64_Xword   sh_size;            /* Size of section */
  Elf64_Word    sh_link;            /* Link to other section */
  Elf64_Word    sh_info;            /* Miscellaneous information */
  Elf64_Xword   sh_addralign;       /* Address alignment boundary */
  Elf64_Xword   sh_entsize;         /* Size of entries, if section has table */
};

class elf_readert
{
public:
  explicit elf_readert(std::istream &_in);

  enum elf_classt { ELF32=1, ELF64=2 };
  elf_classt elf_class;

  // the ELF header
  Elf32_Ehdr elf32_header;
  Elf64_Ehdr elf64_header;

  bool little_endian;

  // section header table
  using elf32_section_header_tablet = std::vector<Elf32_Shdr>;
  elf32_section_header_tablet elf32_section_header_table;

  using elf64_section_header_tablet = std::vector<Elf64_Shdr>;
  elf64_section_header_tablet elf64_section_header_table;

  // string table
  std::streampos string_table_offset;
  std::string get_string(std::streampos index) const;

  std::string elf32_section_name(std::size_t index) const
  {
    return get_string(elf32_section_header_table[index].sh_name);
  }

  std::string elf64_section_name(std::size_t index) const
  {
    return get_string(elf64_section_header_table[index].sh_name);
  }

  std::size_t number_of_sections;

  std::string section_name(std::size_t index) const
  {
    return
      elf_class==ELF32?elf32_section_name(index):
                       elf64_section_name(index);
  }

  std::streampos section_offset(std::size_t index) const
  {
    return
      elf_class==ELF32?elf32_section_header_table[index].sh_offset:
                       elf64_section_header_table[index].sh_offset;
  }

  bool has_section(const std::string &name) const;

protected:
  std::istream &in;
};

#endif // CPROVER_GOTO_PROGRAMS_ELF_READER_H

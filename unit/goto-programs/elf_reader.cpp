/*******************************************************************\

Module: Unit tests for ELF reader

Author: Daniel Kroening

\*******************************************************************/

#include <util/exception_utils.h>

#include <goto-programs/elf_reader.h>

#include <testing-utils/use_catch.h>

#include <cstdint>
#include <sstream>
#include <string>

TEST_CASE(
  "ELF reader handles invalid input",
  "[core][goto-programs][elf_reader]")
{
  std::istringstream in("not an ELF file");

  REQUIRE_THROWS_AS(elf_readert(in), deserialization_exceptiont);
}

namespace
{
void append_le16(std::string &bytes, uint16_t value)
{
  bytes += static_cast<char>(value & 0xff);
  bytes += static_cast<char>((value >> 8) & 0xff);
}

void append_le32(std::string &bytes, uint32_t value)
{
  bytes += static_cast<char>(value & 0xff);
  bytes += static_cast<char>((value >> 8) & 0xff);
  bytes += static_cast<char>((value >> 16) & 0xff);
  bytes += static_cast<char>((value >> 24) & 0xff);
}

// A well-formed little-endian ELF32 with two sections: the mandatory
// SHT_NULL section at index 0 and a .shstrtab string table at index 1.
// Layout: 52-byte header, then a 2-entry (40 bytes each) section header
// table at offset 52, then the string table contents at offset 132.
std::string minimal_elf32()
{
  const uint32_t header_size = 52;
  const uint32_t section_entry_size = 40;
  const uint32_t section_count = 2;
  const uint32_t string_table_offset =
    header_size + section_count * section_entry_size; // 132
  const std::string string_table = std::string("\0.shstrtab", 10) + '\0';

  std::string elf;

  // e_ident
  elf += '\x7f';
  elf += 'E';
  elf += 'L';
  elf += 'F';
  elf += '\x01';                   // EI_CLASS = ELFCLASS32
  elf += '\x01';                   // EI_DATA  = little-endian
  elf.append(EI_NIDENT - 6, '\0'); // padding to 16 bytes

  append_le16(elf, 1);                  // e_type    = ET_REL
  append_le16(elf, 0);                  // e_machine
  append_le32(elf, 1);                  // e_version = EV_CURRENT (required)
  append_le32(elf, 0);                  // e_entry
  append_le32(elf, 0);                  // e_phoff
  append_le32(elf, header_size);        // e_shoff
  append_le32(elf, 0);                  // e_flags
  append_le16(elf, header_size);        // e_ehsize
  append_le16(elf, 0);                  // e_phentsize
  append_le16(elf, 0);                  // e_phnum
  append_le16(elf, section_entry_size); // e_shentsize
  append_le16(elf, section_count);      // e_shnum
  append_le16(elf, 1);                  // e_shstrndx -> .shstrtab

  // section header 0: SHT_NULL (all zero)
  elf.append(section_entry_size, '\0');

  // section header 1: .shstrtab
  append_le32(elf, 1);                   // sh_name -> ".."
  append_le32(elf, 3);                   // sh_type = STRTAB
  append_le32(elf, 0);                   // sh_flags
  append_le32(elf, 0);                   // sh_addr
  append_le32(elf, string_table_offset); // sh_offset
  append_le32(elf, static_cast<uint32_t>(string_table.size())); // sh_size
  append_le32(elf, 0);                                          // sh_link
  append_le32(elf, 0);                                          // sh_info
  append_le32(elf, 1);                                          // sh_addralign
  append_le32(elf, 0);                                          // sh_entsize

  // string table contents: "\0.shstrtab\0"
  elf += string_table;

  return elf;
}
} // namespace

TEST_CASE(
  "ELF reader parses a minimal ELF32",
  "[core][goto-programs][elf_reader]")
{
  std::istringstream in(minimal_elf32());
  elf_readert elf_reader(in);

  REQUIRE(elf_reader.number_of_sections == 2);
  REQUIRE(elf_reader.section_name(1) == ".shstrtab");
  REQUIRE(elf_reader.has_section(".shstrtab"));
  REQUIRE_FALSE(elf_reader.has_section(".text"));
}

TEST_CASE(
  "ELF reader rejects a malformed ELF32",
  "[core][goto-programs][elf_reader]")
{
  // An "almost" ELF32: valid magic and class, so the reader commits to ELF32
  // parsing, but the e_version field (offset 20, required to be 1) is zeroed
  // out. Everything else is well-formed, so this exercises a deeper header
  // validation path than the non-ELF case above.
  std::string elf = minimal_elf32();
  elf[20] = '\0';
  elf[21] = '\0';
  elf[22] = '\0';
  elf[23] = '\0';

  std::istringstream in(elf);
  REQUIRE_THROWS_AS(elf_readert(in), deserialization_exceptiont);
}

/*******************************************************************\

Module: Unit tests for is_goto_binary

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <goto-programs/read_goto_binary.h>
#include <util/message.h>

#include <sstream>

TEST_CASE("is_goto_binary", "[core][goto-programs][is_goto_binary]")
{
  std::string class_file("goto-programs/Hello.class");
  std::string fat_macho("goto-programs/hello_fat_macho");
  std::string fat_macho_with_gbf("goto-programs/hello_fat_macho_with_gbf");
  std::string elf("goto-programs/hello_elf");
  std::string elf_with_gbf("goto-programs/hello_elf_with_gbf");

  std::ostringstream fat_macho_output;
  stream_message_handlert fat_macho_output_handler(fat_macho_output);
  std::ostringstream fat_macho_with_gbf_output;
  stream_message_handlert fat_macho_with_gbf_output_handler(
    fat_macho_with_gbf_output);
  std::ostringstream elf_output;
  stream_message_handlert elf_output_handler(elf_output);
  std::ostringstream elf_with_gbf_output;
  stream_message_handlert elf_with_gbf_output_handler(elf_with_gbf_output);
  std::ostringstream class_file_output;
  stream_message_handlert class_file_output_handler(class_file_output);

  bool class_file_is_gbf =
    is_goto_binary(class_file, class_file_output_handler);
  REQUIRE(!class_file_is_gbf);
  REQUIRE(class_file_output.str().empty());

  bool elf_has_gbf = is_goto_binary(elf, elf_output_handler);
  bool elf_with_gbf_has_gbf =
    is_goto_binary(elf_with_gbf, elf_with_gbf_output_handler);
  REQUIRE(!elf_has_gbf);
  REQUIRE(elf_with_gbf_has_gbf);
  REQUIRE(elf_output.str().empty());
  REQUIRE(elf_with_gbf_output.str().empty());

  bool fat_macho_has_gbf = is_goto_binary(fat_macho, fat_macho_output_handler);
  bool fat_macho_with_gbf_has_gbf =
    is_goto_binary(fat_macho_with_gbf, fat_macho_with_gbf_output_handler);

#ifdef __APPLE__

  REQUIRE(!fat_macho_has_gbf);
  REQUIRE(fat_macho_output.str().empty());
  REQUIRE(fat_macho_with_gbf_has_gbf);
  REQUIRE(fat_macho_with_gbf_output.str().empty());

#else

  REQUIRE(!fat_macho_has_gbf);
  REQUIRE(
    fat_macho_output.str() == "Cannot read OSX fat archive on this platform\n");

  REQUIRE(!fat_macho_with_gbf_has_gbf);
  REQUIRE(
    fat_macho_with_gbf_output.str() ==
    "Cannot read OSX fat archive on this platform\n");

#endif
}

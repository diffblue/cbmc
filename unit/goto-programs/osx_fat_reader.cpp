/*******************************************************************\

Module: Unit tests for osx_fat_binary

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <goto-programs/osx_fat_reader.h>
#ifdef __APPLE__
#include <util/exception_utils.h>
#endif

#include <fstream>

TEST_CASE("OSX fat binary reader", "[core][goto-programs][osx_fat_reader]")
{
  std::ifstream class_file("goto-programs/Hello.class");
  std::ifstream fat_macho("goto-programs/hello_fat_macho");
  std::ifstream fat_macho_with_gbf("goto-programs/hello_fat_macho_with_gbf");

  char class_header[8];
  char fat_macho_header[8];
  char fat_macho_with_gbf_header[8];

  class_file.read(class_header, 8);
  fat_macho.read(fat_macho_header, 8);
  fat_macho_with_gbf.read(fat_macho_with_gbf_header, 8);

  REQUIRE(class_file);
  REQUIRE(fat_macho);
  REQUIRE(fat_macho_with_gbf);

  REQUIRE(is_osx_fat_header(fat_macho_header));
  REQUIRE(is_osx_fat_header(fat_macho_with_gbf_header));
  REQUIRE(!is_osx_fat_header(class_header));

  class_file.seekg(0);
  fat_macho.seekg(0);
  fat_macho_with_gbf.seekg(0);

  std::ostringstream fat_macho_output;
  stream_message_handlert fat_macho_output_handler(fat_macho_output);
  std::ostringstream fat_macho_with_gbf_output;
  stream_message_handlert fat_macho_with_gbf_output_handler(
    fat_macho_with_gbf_output);
  std::ostringstream class_file_output;
  stream_message_handlert class_file_output_handler(class_file_output);

#ifdef __APPLE__

  REQUIRE_THROWS_AS(
    (osx_fat_readert{class_file, class_file_output_handler}),
    deserialization_exceptiont);

  osx_fat_readert fat_macho_reader(fat_macho, fat_macho_output_handler);
  REQUIRE(fat_macho_output.str().empty());
  REQUIRE(!fat_macho_reader.has_gb());

  osx_fat_readert fat_macho_with_gbf_reader(
    fat_macho_with_gbf, fat_macho_with_gbf_output_handler);
  REQUIRE(fat_macho_with_gbf_output.str().empty());
  REQUIRE(fat_macho_with_gbf_reader.has_gb());

#else

  osx_fat_readert class_file_reader(class_file, class_file_output_handler);
  REQUIRE(!class_file_reader.has_gb());
  REQUIRE(
    class_file_output.str() ==
    "Cannot read OSX fat archive on this platform\n");

  osx_fat_readert fat_macho_reader(fat_macho, fat_macho_output_handler);
  REQUIRE(!fat_macho_reader.has_gb());
  REQUIRE(
    fat_macho_output.str() == "Cannot read OSX fat archive on this platform\n");

  osx_fat_readert fat_macho_with_gbf_reader(
    fat_macho_with_gbf, fat_macho_with_gbf_output_handler);
  REQUIRE(!fat_macho_with_gbf_reader.has_gb());
  REQUIRE(
    fat_macho_with_gbf_output.str() ==
    "Cannot read OSX fat archive on this platform\n");

#endif
}

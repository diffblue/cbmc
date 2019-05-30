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
  std::ifstream fat_binary("goto-programs/hello_fat");

  char class_header[8];
  char fat_binary_header[8];

  class_file.read(class_header, 8);
  fat_binary.read(fat_binary_header, 8);

  REQUIRE(class_file);
  REQUIRE(fat_binary);

  REQUIRE(is_osx_fat_header(fat_binary_header));
  REQUIRE(!is_osx_fat_header(class_header));

  class_file.seekg(0);
  fat_binary.seekg(0);

  std::ostringstream fat_binary_output;
  stream_message_handlert fat_binary_output_handler(fat_binary_output);
  std::ostringstream class_file_output;
  stream_message_handlert class_file_output_handler(class_file_output);

#ifdef __APPLE__

  REQUIRE_THROWS_AS(
    (osx_fat_readert{class_file, class_file_output_handler}),
    deserialization_exceptiont);
  osx_fat_readert fat_binary_reader(fat_binary, fat_binary_output_handler);
  REQUIRE(fat_binary_output.str().empty());
  REQUIRE(!fat_binary_reader.has_gb());

#else

  osx_fat_readert class_file_reader(class_file, class_file_output_handler);
  REQUIRE(!class_file_reader.has_gb());
  REQUIRE(
    class_file_output.str() ==
    "Cannot read OSX fat archive on this platform\n");

  osx_fat_readert fat_binary_reader(fat_binary, fat_binary_output_handler);
  REQUIRE(!fat_binary_reader.has_gb());
  REQUIRE(
    fat_binary_output.str() ==
    "Cannot read OSX fat archive on this platform\n");

#endif
}

/*******************************************************************\

Module: Unit test for get_base_name.h

Author: Daniel Kroening

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/get_base_name.h>

TEST_CASE("get_base_name basic functionality", "[core][util][get_base_name]")
{
  REQUIRE(get_base_name(".exe", true) == "");
  REQUIRE(get_base_name(".exe", false) == ".exe");
  REQUIRE(get_base_name(".", true) == "");
  REQUIRE(get_base_name(".", false) == ".");
  REQUIRE(get_base_name("some.file.ext", true) == "some.file");
  REQUIRE(get_base_name("some.file.ext", false) == "some.file.ext");
  REQUIRE(get_base_name("/.exe", true) == "");
  REQUIRE(get_base_name("/.exe", false) == ".exe");
  REQUIRE(get_base_name("/file.exe", true) == "file");
  REQUIRE(get_base_name("/file.exe", false) == "file.exe");
  REQUIRE(get_base_name("some.dir/file", true) == "file");
  REQUIRE(get_base_name("some.dir/file", false) == "file");
  REQUIRE(get_base_name("/some.dir/file", true) == "file");
  REQUIRE(get_base_name("/some.dir/file", false) == "file");
#ifdef _WIN32
  REQUIRE(get_base_name("dir\\file", true) == "file");
  REQUIRE(get_base_name("some.dir\\file", true) == "file");
#else
  REQUIRE(get_base_name("dir\\file", true) == "dir\\file");
  REQUIRE(get_base_name("some.dir\\file", true) == "some");
#endif
}

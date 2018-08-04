/*******************************************************************\

Module: Unit tests for file_util.h

Author: Daniel Kroening

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/file_util.h>
#include <util/tempdir.h>
#include <util/unicode.h>

#include <fstream>

TEST_CASE("is_directory functionality", "[core][util][file_util]")
{
  temp_dirt temp_dir("testXXXXXX");

  #ifdef _WIN32
  std::ofstream outfile(widen(temp_dir("file")));
  #else
  std::ofstream outfile(temp_dir("file"));
  #endif

  outfile.close();

  REQUIRE(is_directory(temp_dir.path));
  REQUIRE(is_directory(temp_dir.path+"/"));
  REQUIRE(!is_directory(temp_dir("whatnot")));
  REQUIRE(!is_directory(temp_dir("file")));
  REQUIRE(!is_directory(""));
}

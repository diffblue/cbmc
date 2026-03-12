/*******************************************************************\

Module: Output File Container

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// output_filet unit tests

#include <util/exception_utils.h>
#include <util/output_file.h>
#include <util/tempfile.h>

#include <testing-utils/use_catch.h>

#include <fstream>

TEST_CASE("output_filet writes to file", "[core][util][output_file]")
{
  temporary_filet tmp("output_filet_test", ".txt");
  const std::string filename = tmp();

  {
    output_filet out(filename);
    REQUIRE(out.name() == filename);
    REQUIRE(out.is_file());
    out.stream() << "hello";
  }

  std::ifstream in(filename);
  std::string content;
  std::getline(in, content);
  REQUIRE(content == "hello");
}

TEST_CASE("output_filet stdout for dash", "[core][util][output_file]")
{
  output_filet out("-");
  REQUIRE(out.name() == "stdout");
  REQUIRE_FALSE(out.is_file());
}

TEST_CASE("output_filet throws on invalid path", "[core][util][output_file]")
{
  temporary_filet tmp("output_filet_test", "");
  // Use the temp file path as a "directory" — opening a file beneath it fails
  const std::string bad_path = tmp() + "/file.txt";
  REQUIRE_THROWS_AS(output_filet(bad_path), system_exceptiont);
}

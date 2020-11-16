/*******************************************************************\

Module: Unit test for run.h/run.cpp

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/run.h>
#include <util/tempfile.h>

#include <fstream>

SCENARIO("run() error reporting", "[core][util][run]")
{
  GIVEN("A command invoking a non-existent executable")
  {
    temporary_filet tmp_stderr("tmp.txt", "");

    int result =
      run("no-such-binary", {"no-such-binary"}, "", "", tmp_stderr());

    THEN("run returns a non-zero exit code")
    {
      REQUIRE(result != 0);
    }
    THEN("run provides an error message")
    {
      std::ifstream read_output{tmp_stderr()};
      std::string line;
      REQUIRE(std::getline(read_output, line));
#ifdef _WIN32
      // strip terminating \r
      REQUIRE(
        Catch::trim(line) == "The system cannot find the file specified.");
#else
      REQUIRE(
        line == "execvp no-such-binary failed: No such file or directory");
#endif
    }
  }
}

/*******************************************************************\

Module: Unit tests for file_util.h

Author: Daniel Kroening

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/exception_utils.h>
#include <util/file_util.h>
#include <util/tempdir.h>
#include <util/unicode.h>

#include <fstream>

TEST_CASE("concat_dir_file functionality", "[core][util][file_util]")
{
  temp_dirt temp_dir("testXXXXXX");
  const std::string path = concat_dir_file(temp_dir.path, "bla.txt");

  REQUIRE(path.size() > temp_dir.path.size() + std::string("bla.txt").size());
#ifdef _WIN32
  REQUIRE(path.find('\\') != std::string::npos);
#else
  REQUIRE(path.find('/') != std::string::npos);
#endif

#ifdef _WIN32
  const std::string qualified_path = "z:\\some\\path\\foo.txt";
#else
  const std::string qualified_path = "/some/path/foo.txt";
#endif
  const std::string path2 = concat_dir_file(temp_dir.path, qualified_path);
  REQUIRE(path2 == qualified_path);
}

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

TEST_CASE("get/set working directory", "[core][util][file_util]")
{
  temp_dirt temp_dir("testXXXXXX");

  std::string cwd = get_current_working_directory();
  REQUIRE(cwd != temp_dir.path);
  set_current_path(temp_dir.path);
  REQUIRE(get_current_working_directory() == temp_dir.path);
  REQUIRE_THROWS_AS(set_current_path("no-such-dir"), system_exceptiont);

  set_current_path(cwd);
}

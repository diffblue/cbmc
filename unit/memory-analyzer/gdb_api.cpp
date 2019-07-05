/*******************************************************************\

Module: GDB Machine Interface API unit tests

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <cstdio>
#include <regex>
#include <string>
#include <vector>

#include <fstream>
#include <iostream>

#include <memory-analyzer/gdb_api.cpp>
#include <util/run.h>

void compile_test_file()
{
  REQUIRE(
    run("gcc", {"gcc", "-g", "-o", "test", "memory-analyzer/test.c"}) == 0);
}

void check_for_gdb()
{
  REQUIRE(run("gdb", {"gdb", "--version"}, "", "/dev/null", "/dev/null") == 0);
}

class gdb_api_testt : public gdb_apit
{
public:
  explicit gdb_api_testt(const std::vector<std::string> &args) : gdb_apit(args)
  {
  }

  friend void gdb_api_internals_test();

  using gdb_apit::r_hex_addr;
};

void gdb_api_internals_test()
{
  check_for_gdb();
  compile_test_file();

  std::vector<std::string> args;
  args.push_back("test");

  SECTION("parse gdb output record")
  {
    gdb_api_testt gdb_api(args);

    gdb_api_testt::gdb_output_recordt gor = gdb_api.parse_gdb_output_record(
      "a = \"1\", b = \"2\", c = {1, 2}, d = [3, 4], e=\"0x0\"");

    REQUIRE(gor["a"] == "1");
    REQUIRE(gor["b"] == "2");
    REQUIRE(gor["c"] == "{1, 2}");
    REQUIRE(gor["d"] == "[3, 4]");
    REQUIRE(gor["e"] == "0x0");
  }

  SECTION("read a line from an input stream")
  {
    gdb_api_testt gdb_api(args);

    FILE *f = fopen("memory-analyzer/input.txt", "r");
    gdb_api.response_stream = f;

    std::string line = gdb_api.read_next_line();
    REQUIRE(line == "abc\n");

    line = gdb_api.read_next_line();
    REQUIRE(line == std::string(1120, 'a') + "\n");

    line = gdb_api.read_next_line();
    REQUIRE(line == "xyz");
  }

  SECTION("start and exit gdb")
  {
    gdb_api_testt gdb_api(args);

    gdb_api.create_gdb_process();

    // check input and output streams
    REQUIRE(!ferror(gdb_api.response_stream));
    REQUIRE(!ferror(gdb_api.command_stream));
  }
}

TEST_CASE("gdb api internals test", "[core][memory-analyzer]")
{
  gdb_api_internals_test();
}

TEST_CASE("gdb api test", "[core][memory-analyzer]")
{
  check_for_gdb();
  compile_test_file();

  std::vector<std::string> args;
  args.push_back("test");

  {
    gdb_apit gdb_api(args, true);
    gdb_api.create_gdb_process();

    try
    {
      const bool r = gdb_api.run_gdb_to_breakpoint("checkpoint");
      REQUIRE(r);
    }
    catch(const gdb_interaction_exceptiont &e)
    {
      std::cerr << "warning: cannot fully unit test GDB API as program cannot "
                << "be run with gdb\n";
      std::cerr << "warning: this may be due to not having the required "
                << "permissions (e.g., to invoke ptrace() or to disable ASLR)"
                << "\n";
      std::cerr << "gdb_interaction_exceptiont:" << '\n';
      std::cerr << e.what() << '\n';

      std::ifstream file("gdb.txt");
      CHECK_RETURN(file.is_open());
      std::string line;

      std::cerr << "=== gdb log begin ===\n";

      while(getline(file, line))
      {
        std::cerr << line << '\n';
      }

      file.close();

      std::cerr << "=== gdb log end ===\n";

      return;
    }
  }

  gdb_api_testt gdb_api(args);

  std::regex hex_addr(gdb_api.r_hex_addr);

  gdb_api.create_gdb_process();

  SECTION("breakpoint is hit")
  {
    const bool r = gdb_api.run_gdb_to_breakpoint("checkpoint");
    REQUIRE(r);
  }

  SECTION("breakpoint is not hit")
  {
    const bool r = gdb_api.run_gdb_to_breakpoint("checkpoint2");
    REQUIRE(!r);
  }

  SECTION("breakpoint does not exist")
  {
    REQUIRE_THROWS_AS(
      gdb_api.run_gdb_to_breakpoint("checkpoint3"), gdb_interaction_exceptiont);
  }

  SECTION("query variables, primitive types")
  {
    const bool r = gdb_api.run_gdb_to_breakpoint("checkpoint");
    REQUIRE(r);

    const auto &x_value = gdb_api.get_value("x");
    const auto &y_value = gdb_api.get_value("y");
    const auto &z_value = gdb_api.get_value("z");

    REQUIRE(x_value.has_value());
    REQUIRE(*x_value == "8");
    REQUIRE(y_value.has_value());
    REQUIRE(*y_value == "2.5");
    REQUIRE(z_value.has_value());
    REQUIRE(*z_value == "c");
  }

  SECTION("query pointers")
  {
    const bool r = gdb_api.run_gdb_to_breakpoint("checkpoint");
    REQUIRE(r);

    {
      auto value = gdb_api.get_memory("s");
      REQUIRE(std::regex_match(value.address.string(), hex_addr));
      REQUIRE(value.pointee.empty());
      REQUIRE(value.character.empty());
      REQUIRE(*value.string == "abc");
    }

    {
      auto value = gdb_api.get_memory("p");
      REQUIRE(std::regex_match(value.address.string(), hex_addr));
      REQUIRE(value.pointee == "x");
      REQUIRE(value.character.empty());
      REQUIRE(!value.string);
    }

    {
      auto value = gdb_api.get_memory("vp");
      REQUIRE(std::regex_match(value.address.string(), hex_addr));
      REQUIRE(value.pointee == "x");
      REQUIRE(value.character.empty());
      REQUIRE(!value.string);
    }

    {
      auto value = gdb_api.get_memory("np");
      REQUIRE(value.address.is_null());
      REQUIRE(value.pointee.empty());
      REQUIRE(value.character.empty());
      REQUIRE(!value.string);
    }

    {
      auto value = gdb_api.get_memory("vp_string");
      REQUIRE(std::regex_match(value.address.string(), hex_addr));
      REQUIRE(value.pointee.empty());
      REQUIRE(value.character.empty());
      REQUIRE(!value.string);
    }
  }

  SECTION("query expressions")
  {
    const bool r = gdb_api.run_gdb_to_breakpoint("checkpoint");
    REQUIRE(r);

    {
      auto value = gdb_api.get_memory("&x");
      REQUIRE(std::regex_match(value.address.string(), hex_addr));
      REQUIRE(value.pointee == "x");
      REQUIRE(value.character.empty());
      REQUIRE(!value.string);
    }
  }
}

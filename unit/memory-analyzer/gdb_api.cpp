/*******************************************************************\

Module: GDB Machine Interface API unit tests

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

#include <testing-utils/use_catch.h>

#ifdef __linux__
//  \file Test that the regex expression used work as expected.
#define private public
#include <memory-analyzer/gdb_api.cpp>
#include <string>

SCENARIO(
  "gdb_apit uses regex as expected for memory",
  "[core][memory-analyzer]")
{
  gdb_apit gdb_api("");
  GIVEN("The result of a struct pointer")
  {
    const std::string line = "$2 = (struct cycle_buffer *) 0x601050 <buffer>";
    THEN("the result matches the memory address in the output")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x601050");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x601050");
    }
  }

  GIVEN("The result of a typedef pointer")
  {
    const std::string line = "$4 = (cycle_buffer_entry_t *) 0x602010";
    THEN("the result matches the memory address in the output")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x602010");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x602010");
    }
  }

  GIVEN("The result of a char pointer")
  {
    const std::string line = "$5 = 0x400734 \"snow\"";
    THEN("the result matches the memory address in the output")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x400734");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x400734");
    }
  }

  GIVEN("The result of a null pointer")
  {
    const std::string line = "$2 = 0x0";
    THEN("the result matches the memory address in the output")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x0");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x0");
    }
  }

  GIVEN("The result of a char pointer at very low address")
  {
    const std::string line = "$34 = 0x007456 \"snow\"";
    THEN("the result matches the memory address and not nullpointer")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x007456");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x007456");
    }
  }

  GIVEN("The result of a char pointer with some more whitespaces")
  {
    const std::string line = "$12 = 0x400752 \"thunder storm\"\n";
    THEN("the result matches the memory address in the output")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x400752");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x400752");
    }
  }

  GIVEN("The result of an array pointer")
  {
    const std::string line = "$5 = (struct a_sub_type_t (*)[4]) 0x602080";
    THEN("the result matches the memory address in the output")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x602080");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x602080");
    }
  }

  GIVEN("A constant struct pointer pointing to 0x0")
  {
    const std::string line = "$3 = (const struct name *) 0x0";
    THEN("the returned memory address should be 0x0")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x0");
    }
  }

  GIVEN("An enum address")
  {
    const std::string line = "$2 = (char *(*)[5]) 0x7e5500 <abc>";
    THEN("the returned address is the address of the enum")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x7e5500");
    }
  }

  GIVEN("The result of an int pointer")
  {
    const std::string line = "$1 = (int *) 0x601088 <e>\n";
    THEN("the result is the value of memory address of the int pointer")
    {
      REQUIRE(gdb_api.extract_memory(line) == "0x601088");
    }
    THEN("adding '(gdb) ' to the line doesn't have an influence")
    {
      REQUIRE(gdb_api.extract_memory("(gdb) " + line) == "0x601088");
    }
  }

  GIVEN("Non matching result")
  {
    const std::string line = "Something that must not match 0x605940";
    THEN("an exception is thrown")
    {
      REQUIRE_THROWS_AS(
        gdb_api.extract_memory(line), gdb_interaction_exceptiont);
    }
  }
}

SCENARIO(
  "gdb_apit uses regex as expected for value extraction",
  "[core][memory-analyzer]")
{
  gdb_apit gdb_api("");
  GIVEN("An integer value")
  {
    const std::string line = "$90 = 100";
    THEN("the result schould be '100'")
    {
      REQUIRE(gdb_api.extract_value(line) == "100");
    }
  }

  GIVEN("A string value")
  {
    const std::string line = "$5 = 0x602010 \"snow\"";
    THEN("the result should be 'snow'")
    {
      REQUIRE(gdb_api.extract_value(line) == "snow");
    }
  }

  GIVEN("A string with withe spaces")
  {
    const std::string line = "$1323 = 0x1243253 \"thunder storm\"\n";
    THEN("the result should be 'thunder storm'")
    {
      REQUIRE(gdb_api.extract_value(line) == "thunder storm");
    }
  }

  GIVEN("A byte value")
  {
    const std::string line = "$2 = 243 '\363'";
    THEN("the result should be 243")
    {
      REQUIRE(gdb_api.extract_value(line) == "243");
    }
  }

  GIVEN("A negative int value")
  {
    const std::string line = "$8 = -32";
    THEN("the result should be -32")
    {
      REQUIRE(gdb_api.extract_value(line) == "-32");
    }
  }

  GIVEN("An enum value")
  {
    const std::string line = "$1 = INFO";
    THEN("the result should be INFO")
    {
      REQUIRE(gdb_api.extract_value(line) == "INFO");
    }
  }

  GIVEN("A void pointer value")
  {
    const std::string line = "$6 = (const void *) 0x71";
    THEN("the requried result should be 0x71")
    {
      REQUIRE(gdb_api.extract_value(line) == "0x71");
    }
  }

  GIVEN("A gdb response that contains 'cannot access memory'")
  {
    const std::string line = "Cannot access memory at address 0x71";
    THEN("a gdb_inaccesible_memoryt excepition must be raised")
    {
      REQUIRE_THROWS_AS(
        gdb_api.extract_value(line), gdb_inaccessible_memory_exceptiont);
    }
  }

  GIVEN("A value that must not match")
  {
    const std::string line = "$90 = must not match 20";
    THEN("an exception is raised")
    {
      REQUIRE_THROWS_AS(
        gdb_api.extract_value(line), gdb_interaction_exceptiont);
    }
  }
}
#endif

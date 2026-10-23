/*******************************************************************\

Module: Unit tests for basic block detection

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/std_expr.h>

#include <goto-programs/goto_program.h>

#include <analyses/basic_blocks.h>
#include <testing-utils/use_catch.h>

static source_locationt make_location(const char *file, const char *line)
{
  source_locationt location;
  location.set_file(file);
  location.set_line(line);
  return location;
}

SCENARIO(
  "basic block detection for C/C++ goto programs",
  "[core][analyses][basic_blocks]")
{
  GIVEN("a straight-line program with an assume in the middle")
  {
    // SKIP; ASSUME(true); SKIP; END_FUNCTION
    goto_programt program;
    const auto skip_before =
      program.add(goto_programt::make_skip(make_location("test.c", "1")));
    const auto assume = program.add(goto_programt::make_assumption(
      true_exprt{}, make_location("test.c", "2")));
    const auto skip_after =
      program.add(goto_programt::make_skip(make_location("test.c", "3")));
    program.add(goto_programt::make_end_function(make_location("test.c", "3")));
    program.update();

    const goto_programt::const_targett before = skip_before;
    const goto_programt::const_targett the_assume = assume;
    const goto_programt::const_targett after = skip_after;

    WHEN("assume statements delimit blocks (the default)")
    {
      const basic_blockst blocks{program};

      THEN("the assume terminates its block")
      {
        REQUIRE(blocks.size() == 2);
        REQUIRE(blocks.block_of(before) == blocks.block_of(the_assume));
        REQUIRE(blocks.block_of(after) != blocks.block_of(before));
      }
    }

    WHEN("assume statements do not delimit blocks")
    {
      const basic_blockst blocks{program, basic_block_configt{false}};

      THEN("the whole straight-line program is a single block")
      {
        REQUIRE(blocks.size() == 1);
        REQUIRE(blocks.block_of(before) == blocks.block_of(after));
      }
    }
  }
}

SCENARIO(
  "basic block detection for Java goto programs",
  "[core][analyses][basic_blocks]")
{
  GIVEN("a program whose instructions carry Java bytecode indices")
  {
    const auto with_index = [](const char *index)
    {
      source_locationt location;
      location.set_java_bytecode_index(index);
      return location;
    };

    goto_programt program;
    // Two instructions at bytecode index 0, then one at index 1.
    const auto first = program.add(goto_programt::make_skip(with_index("0")));
    const auto second = program.add(goto_programt::make_skip(with_index("0")));
    const auto third = program.add(goto_programt::make_skip(with_index("1")));
    program.add(goto_programt::make_end_function(with_index("1")));
    program.update();

    WHEN("blocks are detected by bytecode index")
    {
      const java_basic_blockst blocks{program};

      THEN("instructions are grouped per bytecode index")
      {
        REQUIRE(blocks.size() == 2);
        REQUIRE(
          blocks.block_of(goto_programt::const_targett{first}) ==
          blocks.block_of(goto_programt::const_targett{second}));
        REQUIRE(
          blocks.block_of(goto_programt::const_targett{third}) !=
          blocks.block_of(goto_programt::const_targett{first}));
      }
    }
  }
}

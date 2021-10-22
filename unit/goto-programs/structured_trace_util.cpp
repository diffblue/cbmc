/*******************************************************************\

Module: structured_trace_util

Author: Diffblue

\*******************************************************************/
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_trace.h>
#include <goto-programs/structured_trace_util.h>

void link_edges(goto_programt::targett source, goto_programt::targett target)
{
  source->targets.push_back(target);
  target->incoming_edges.insert(source);
}

source_locationt simple_location(const std::string &file, unsigned line)
{
  source_locationt location;
  location.set_file(file);
  location.set_line(line);
  return location;
}

goto_programt::targett add_instruction(
  const source_locationt &location,
  goto_programt::instructionst &instructions)
{
  goto_programt::instructiont instruction;
  instruction.location_number = instructions.size();
  instruction.source_location_nonconst() = location;
  instructions.push_back(instruction);
  return std::next(instructions.begin(), instruction.location_number);
}

TEST_CASE("structured_trace_util", "[core][util][trace]")
{
  goto_programt::instructionst instructions;

  source_locationt nil_location;

  const source_locationt unrelated_location = simple_location("foo.c", 1);

  source_locationt no_file_location;
  no_file_location.set_line(1);

  const source_locationt basic_location = simple_location("test.c", 1);
  const source_locationt loop_head_location = simple_location("test.c", 2);
  const source_locationt back_edge_location = simple_location("test.c", 3);

  // 0 # normal_location
  add_instruction(basic_location, instructions);
  // 1 # loop_head
  add_instruction(loop_head_location, instructions);
  // 2: goto 1 # back_edge
  const auto back_edge = add_instruction(back_edge_location, instructions);
  back_edge->type_nonconst() = GOTO;
  // 3: no_location
  goto_programt::instructiont no_location;
  no_location.location_number = 3;
  instructions.push_back(no_location);
  // 4: no_file
  add_instruction(no_file_location, instructions);

  link_edges(
    std::next(instructions.begin(), 2), std::next(instructions.begin(), 1));

  SECTION("location-only steps")
  {
    goto_trace_stept step;
    step.step_nr = 1;
    step.thread_nr = 2;
    step.hidden = true;
    SECTION("Simple step")
    {
      step.pc = instructions.begin();

      const auto parsed_step = default_step(step, unrelated_location);

      REQUIRE(parsed_step);
      REQUIRE(parsed_step->step_number == 1);
      REQUIRE(parsed_step->thread_number == 2);
      REQUIRE(parsed_step->hidden);
      REQUIRE(parsed_step->kind == default_step_kindt::LOCATION_ONLY);
      REQUIRE(parsed_step->location == basic_location);
    }
    SECTION("Invalid previous step")
    {
      step.pc = instructions.begin();

      const auto parsed_step = default_step(step, nil_location);

      REQUIRE(parsed_step);
      REQUIRE(parsed_step->step_number == 1);
      REQUIRE(parsed_step->thread_number == 2);
      REQUIRE(parsed_step->hidden);
      REQUIRE(parsed_step->kind == default_step_kindt::LOCATION_ONLY);
      REQUIRE(parsed_step->location == basic_location);
    }

    SECTION("Duplicate step")
    {
      step.pc = instructions.begin();
      const auto parsed_step = default_step(step, basic_location);
      REQUIRE_FALSE(parsed_step);
    }
    SECTION("No source location")
    {
      step.pc = std::next(instructions.begin(), 3);

      const auto parsed_step = default_step(step, unrelated_location);
      REQUIRE_FALSE(parsed_step);
    }
    SECTION("No file")
    {
      step.pc = std::next(instructions.begin(), 4);

      const auto parsed_step = default_step(step, unrelated_location);
      REQUIRE_FALSE(parsed_step);
    }
  }
  SECTION("Loop head steps")
  {
    goto_trace_stept step;
    step.step_nr = 1;
    step.thread_nr = 2;
    step.hidden = false;
    step.pc = std::next(instructions.begin(), 1);
    SECTION("Simple step")
    {
      const auto parsed_step = default_step(step, unrelated_location);

      REQUIRE(parsed_step);
      REQUIRE(parsed_step->step_number == 1);
      REQUIRE(parsed_step->thread_number == 2);
      REQUIRE_FALSE(parsed_step->hidden);
      REQUIRE(parsed_step->kind == default_step_kindt::LOOP_HEAD);
      REQUIRE(parsed_step->location == loop_head_location);
    }

    SECTION("Duplicate step")
    {
      const auto parsed_step = default_step(step, loop_head_location);
      REQUIRE(parsed_step);
      REQUIRE(parsed_step->step_number == 1);
      REQUIRE(parsed_step->thread_number == 2);
      REQUIRE_FALSE(parsed_step->hidden);
      REQUIRE(parsed_step->kind == default_step_kindt::LOOP_HEAD);
      REQUIRE(parsed_step->location == loop_head_location);
    }
  }
}

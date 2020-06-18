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

TEST_CASE("structured_trace_util", "[core][util][trace]")
{
  goto_programt::instructionst instructions;

  source_locationt nil_location;

  source_locationt unrelated_location;
  unrelated_location.set_file("foo.c");
  unrelated_location.set_line(1);

  source_locationt no_file_location;
  unrelated_location.set_line(1);

  source_locationt basic_location;
  basic_location.set_file("test.c");
  basic_location.set_line(1);

  source_locationt loop_head_location;
  loop_head_location.set_file("test.c");
  loop_head_location.set_line(2);

  source_locationt back_edge_location;
  back_edge_location.set_file("test.c");
  back_edge_location.set_line(3);

  // 0 # normal_location
  // 1 # loop_head
  // 2: goto 1 # back_edge
  // 3: no_location
  // 4: no_file
  goto_programt::instructiont normal_instruction;
  normal_instruction.location_number = 0;
  normal_instruction.source_location = basic_location;
  instructions.push_back(normal_instruction);

  goto_programt::instructiont loop_head;
  loop_head.location_number = 1;
  loop_head.source_location = loop_head_location;
  instructions.push_back(loop_head);

  goto_programt::instructiont back_edge;
  back_edge.source_location = back_edge_location;
  back_edge.location_number = 2;
  back_edge.type = GOTO;
  instructions.push_back(back_edge);

  goto_programt::instructiont no_location;
  no_location.location_number = 3;
  instructions.push_back(no_location);

  goto_programt::instructiont no_file;
  no_file.location_number = 4;
  no_file.source_location = no_file_location;
  instructions.push_back(no_file);

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
    step.hidden = true;
    step.pc = std::next(instructions.begin(), 1);
    SECTION("Simple step")
    {
      const auto parsed_step = default_step(step, unrelated_location);

      REQUIRE(parsed_step);
      REQUIRE(parsed_step->step_number == 1);
      REQUIRE(parsed_step->thread_number == 2);
      REQUIRE(parsed_step->hidden);
      REQUIRE(parsed_step->kind == default_step_kindt::LOOP_HEAD);
      REQUIRE(parsed_step->location == loop_head_location);
    }

    SECTION("Duplicate step")
    {
      const auto parsed_step = default_step(step, loop_head_location);
      REQUIRE(parsed_step);
      REQUIRE(parsed_step->step_number == 1);
      REQUIRE(parsed_step->thread_number == 2);
      REQUIRE(parsed_step->hidden);
      REQUIRE(parsed_step->kind == default_step_kindt::LOOP_HEAD);
      REQUIRE(parsed_step->location == loop_head_location);
    }
  }
}

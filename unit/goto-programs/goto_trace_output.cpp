/*******************************************************************\

Module: Unit tests for goto_trace_stept::output

Author: Diffblue Ltd.

\*******************************************************************/

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_trace.h>
#include <sstream>
#include <testing-utils/use_catch.h>

SCENARIO(
  "Output trace with nil lhs object",
  "[core][goto-programs][goto_trace]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  goto_programt::instructionst instructions;
  instructions.emplace_back(goto_program_instruction_typet::OTHER);
  goto_trace_stept step;
  step.pc = instructions.begin();
  step.type = goto_trace_stept::typet::ATOMIC_BEGIN;

  std::ostringstream oss;
  step.output(ns, oss);

  std::istringstream iss(oss.str());
  std::string line;
  std::getline(iss, line);
  REQUIRE(line == "*** ATOMIC_BEGIN");
  std::getline(iss, line);
  REQUIRE(line == "OTHER");
  std::getline(iss, line);
  REQUIRE(line.empty());
}

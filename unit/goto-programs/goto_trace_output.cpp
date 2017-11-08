/*******************************************************************\

 Module: Unit tests for goto_trace_stept::output

 Author: Diffblue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <goto-programs/goto_program_template.h>
#include <goto-programs/goto_trace.h>
#include <iostream>

SCENARIO(
  "Output trace with nil lhs object",
  "[core][goto-programs][goto_trace]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  goto_programt::instructionst instructions;
  instructions.emplace_back(goto_program_instruction_typet::OTHER);
  auto step = trace_atomic_begint{};
  step.pc = instructions.begin();
  step.output(ns, std::cout);
}

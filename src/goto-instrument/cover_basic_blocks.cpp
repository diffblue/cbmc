/*******************************************************************\

Module: Coverage Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Basic blocks detection for Coverage Instrumentation
/// This file adapts the generic basic block detection utility from
/// src/analyses/basic_blocks.h for use in coverage instrumentation.

#include "cover_basic_blocks.h"

#include <util/message.h>

#include <analyses/basic_blocks.h>

// ============================================================================
// cover_basic_blockst implementation (default C/C++ behavior)
// ============================================================================

cover_basic_blockst::cover_basic_blockst(
  const goto_programt &goto_program,
  const basic_block_configt &config)
  : blocks(goto_program, config)
{
  // Initialize extended information for each block (source lines)
  block_infos.resize(blocks.size());

  // Collect source lines for each instruction
  forall_goto_program_instructions(it, goto_program)
  {
    const std::size_t block_nr = blocks.block_of(it);
    INVARIANT(block_nr < block_infos.size(), "block number out of range");
    add_block_lines(block_infos[block_nr], *it);
  }
}

std::size_t cover_basic_blockst::block_of(goto_programt::const_targett t) const
{
  return blocks.block_of(t);
}

std::optional<goto_programt::const_targett>
cover_basic_blockst::instruction_of(const std::size_t block_nr) const
{
  return blocks.instruction_of(block_nr);
}

const source_locationt &
cover_basic_blockst::source_location_of(const std::size_t block_nr) const
{
  return blocks.source_location_of(block_nr);
}

const source_linest &
cover_basic_blockst::source_lines_of(const std::size_t block_nr) const
{
  INVARIANT(block_nr < block_infos.size(), "block number out of range");
  return block_infos[block_nr].source_lines;
}

void cover_basic_blockst::report_block_anomalies(
  const irep_idt &function_id,
  const goto_programt &goto_program,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  std::set<std::size_t> blocks_seen;
  forall_goto_program_instructions(it, goto_program)
  {
    const std::size_t block_nr = blocks.block_of(it);
    const auto representative_inst = blocks.instruction_of(block_nr);
    const auto &source_location = blocks.source_location_of(block_nr);

    if(
      blocks_seen.insert(block_nr).second &&
      representative_inst == goto_program.instructions.end())
    {
      msg.warning() << "Ignoring block " << (block_nr + 1) << " location "
                    << it->location_number << " " << it->source_location()
                    << " (bytecode-index already instrumented)"
                    << messaget::eom;
    }
    else if(representative_inst == it && source_location.is_nil())
    {
      msg.warning() << "Ignoring block " << (block_nr + 1) << " location "
                    << it->location_number << " " << function_id
                    << " (missing source location)" << messaget::eom;
    }
    // The location numbers printed here are those
    // before the coverage instrumentation.
  }
}

void cover_basic_blockst::output(std::ostream &out) const
{
  // One line per instruction: its source location -> containing block number.
  for(const auto &block_pair : blocks.instruction_blocks())
    out << block_pair.first->source_location() << " -> " << block_pair.second
        << '\n';
}

void cover_basic_blockst::add_block_lines(
  cover_basic_blockst::block_infot &block,
  const goto_programt::instructiont &instruction)
{
  const auto &add_location = [&](const source_locationt &location) {
    const irep_idt &line = location.get_line();
    if(!line.empty())
    {
      block.source_lines.insert(location);
    }
  };
  add_location(instruction.source_location());
  instruction.code().visit_pre([&](const exprt &expr) {
    const auto &location = expr.source_location();
    if(!location.get_function().empty())
      add_location(location);
  });
}

// ============================================================================
// cover_basic_blocks_javat implementation (Java-specific behavior)
// ============================================================================

cover_basic_blocks_javat::cover_basic_blocks_javat(
  const goto_programt &goto_program)
  : blocks(goto_program)
{
  // Initialize source lines for each block
  block_source_lines.resize(blocks.size());

  // Collect source lines for each instruction
  forall_goto_program_instructions(it, goto_program)
  {
    const std::size_t block_nr = blocks.block_of(it);
    INVARIANT(
      block_nr < block_source_lines.size(), "block number out of range");
    const auto &location = it->source_location();
    block_source_lines[block_nr].insert(location);
  }
}

std::size_t
cover_basic_blocks_javat::block_of(goto_programt::const_targett t) const
{
  return blocks.block_of(t);
}

std::optional<goto_programt::const_targett>
cover_basic_blocks_javat::instruction_of(const std::size_t block_nr) const
{
  return blocks.instruction_of(block_nr);
}

const source_locationt &
cover_basic_blocks_javat::source_location_of(const std::size_t block_nr) const
{
  return blocks.source_location_of(block_nr);
}

const source_linest &
cover_basic_blocks_javat::source_lines_of(const std::size_t block_nr) const
{
  PRECONDITION(block_nr < block_source_lines.size());
  return block_source_lines[block_nr];
}

void cover_basic_blocks_javat::output(std::ostream &out) const
{
  for(std::size_t i = 0; i < blocks.size(); ++i)
    out << blocks.source_location_of(i) << " -> " << i << '\n';
}

/*******************************************************************\

Module: Coverage Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Basic blocks detection for Coverage Instrumentation

#include "cover_basic_blocks.h"

#include <util/format_number_range.h>
#include <util/message.h>
#include <util/string2int.h>

optionalt<std::size_t> cover_basic_blockst::continuation_of_block(
  const goto_programt::const_targett &instruction,
  cover_basic_blockst::block_mapt &block_map)
{
  if(instruction->incoming_edges.size() != 1)
    return {};

  const goto_programt::targett in_t = *instruction->incoming_edges.cbegin();
  if(in_t->is_goto() && !in_t->is_backwards_goto() && in_t->guard.is_true())
    return block_map[in_t];

  return {};
}

cover_basic_blockst::cover_basic_blockst(const goto_programt &_goto_program)
{
  bool next_is_target = true;
  std::size_t current_block = 0;

  forall_goto_program_instructions(it, _goto_program)
  {
    // Is it a potential beginning of a block?
    if(next_is_target || it->is_target())
    {
      if(auto block_number = continuation_of_block(it, block_map))
      {
        current_block = *block_number;
      }
      else
      {
        block_infos.emplace_back();
        block_infos.back().representative_inst = it;
        block_infos.back().source_location = source_locationt::nil();
        current_block = block_infos.size() - 1;
      }
    }

    INVARIANT(
      current_block < block_infos.size(), "current block number out of range");
    block_infot &block_info = block_infos.at(current_block);

    block_map[it] = current_block;

    // update lines belonging to block
    const irep_idt &line = it->source_location.get_line();
    if(!line.empty())
      block_info.lines.insert(unsafe_string2unsigned(id2string(line)));

    // set representative program location to instrument
    if(
      !it->source_location.is_nil() &&
      !it->source_location.get_file().empty() &&
      !it->source_location.get_line().empty() &&
      block_info.source_location.is_nil())
    {
      block_info.representative_inst = it; // update
      block_info.source_location = it->source_location;
    }

    next_is_target =
#if 0
      // Disabled for being too messy
      it->is_goto() || it->is_function_call() || it->is_assume();
#else
      it->is_goto() || it->is_function_call();
#endif
  }

  for(auto &block_info : block_infos)
    update_covered_lines(block_info);
}

std::size_t cover_basic_blockst::block_of(goto_programt::const_targett t) const
{
  const auto it = block_map.find(t);
  INVARIANT(it != block_map.end(), "instruction must be part of a block");
  return it->second;
}

optionalt<goto_programt::const_targett>
cover_basic_blockst::instruction_of(const std::size_t block_nr) const
{
  INVARIANT(block_nr < block_infos.size(), "block number out of range");
  return block_infos[block_nr].representative_inst;
}

const source_locationt &
cover_basic_blockst::source_location_of(const std::size_t block_nr) const
{
  INVARIANT(block_nr < block_infos.size(), "block number out of range");
  return block_infos[block_nr].source_location;
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
    const std::size_t block_nr = block_of(it);
    const block_infot &block_info = block_infos.at(block_nr);

    if(
      blocks_seen.insert(block_nr).second &&
      block_info.representative_inst == goto_program.instructions.end())
    {
      msg.warning() << "Ignoring block " << (block_nr + 1) << " location "
                    << it->location_number << " " << it->source_location
                    << " (bytecode-index already instrumented)"
                    << messaget::eom;
    }
    else if(
      block_info.representative_inst == it &&
      block_info.source_location.is_nil())
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
  for(const auto &block_pair : block_map)
    out << block_pair.first->source_location << " -> " << block_pair.second
        << '\n';
}

void cover_basic_blockst::update_covered_lines(block_infot &block_info)
{
  if(block_info.source_location.is_nil())
    return;

  const auto &cover_set = block_info.lines;
  INVARIANT(!cover_set.empty(), "covered lines set must not be empty");
  std::vector<unsigned> line_list(cover_set.begin(), cover_set.end());

  std::string covered_lines = format_number_range(line_list);
  block_info.source_location.set_basic_block_covered_lines(covered_lines);
}

cover_basic_blocks_javat::cover_basic_blocks_javat(
  const goto_programt &_goto_program)
{
  forall_goto_program_instructions(it, _goto_program)
  {
    const auto &location = it->source_location;
    const auto &bytecode_index = location.get_java_bytecode_index();
    if(index_to_block.emplace(bytecode_index, block_infos.size()).second)
    {
      block_infos.push_back(it);
      block_locations.push_back(location);
      block_locations.back().set_basic_block_covered_lines(location.get_line());
    }
  }
}

std::size_t
cover_basic_blocks_javat::block_of(goto_programt::const_targett t) const
{
  const auto &bytecode_index = t->source_location.get_java_bytecode_index();
  const auto it = index_to_block.find(bytecode_index);
  INVARIANT(it != index_to_block.end(), "instruction must be part of a block");
  return it->second;
}

optionalt<goto_programt::const_targett>
cover_basic_blocks_javat::instruction_of(const std::size_t block_nr) const
{
  PRECONDITION(block_nr < block_infos.size());
  return block_infos[block_nr];
}

const source_locationt &
cover_basic_blocks_javat::source_location_of(const std::size_t block_nr) const
{
  PRECONDITION(block_nr < block_locations.size());
  return block_locations[block_nr];
}

void cover_basic_blocks_javat::output(std::ostream &out) const
{
  for(std::size_t i = 0; i < block_locations.size(); ++i)
    out << block_locations[i] << " -> " << i << '\n';
}

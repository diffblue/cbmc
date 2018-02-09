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

optionalt<unsigned> cover_basic_blockst::continuation_of_block(
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
  unsigned current_block = 0;

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

unsigned cover_basic_blockst::block_of(goto_programt::const_targett t) const
{
  const auto it = block_map.find(t);
  INVARIANT(it != block_map.end(), "instruction must be part of a block");
  return it->second;
}

optionalt<goto_programt::const_targett>
cover_basic_blockst::instruction_of(unsigned block_nr) const
{
  INVARIANT(block_nr < block_infos.size(), "block number out of range");
  return block_infos.at(block_nr).representative_inst;
}

const source_locationt &
cover_basic_blockst::source_location_of(unsigned block_nr) const
{
  INVARIANT(block_nr < block_infos.size(), "block number out of range");
  return block_infos.at(block_nr).source_location;
}

void cover_basic_blockst::select_unique_java_bytecode_indices(
  const goto_programt &goto_program,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  std::set<unsigned> blocks_seen;
  std::set<irep_idt> bytecode_indices_seen;

  forall_goto_program_instructions(it, goto_program)
  {
    const unsigned block_nr = block_of(it);
    if(blocks_seen.find(block_nr) != blocks_seen.end())
      continue;

    INVARIANT(block_nr < block_infos.size(), "block number out of range");
    block_infot &block_info = block_infos.at(block_nr);
    if(!block_info.representative_inst)
    {
      if(!it->source_location.get_java_bytecode_index().empty())
      {
        // search for a representative
        if(
          bytecode_indices_seen
            .insert(it->source_location.get_java_bytecode_index())
            .second)
        {
          block_info.representative_inst = it;
          block_info.source_location = it->source_location;
          update_covered_lines(block_info);
          blocks_seen.insert(block_nr);
          msg.debug() << it->function << " block " << (block_nr + 1)
                      << ": location " << it->location_number
                      << ", bytecode-index "
                      << it->source_location.get_java_bytecode_index()
                      << " selected for instrumentation." << messaget::eom;
        }
      }
    }
    else if(it == *block_info.representative_inst)
    {
      // check the existing representative
      if(!it->source_location.get_java_bytecode_index().empty())
      {
        if(
          bytecode_indices_seen
            .insert(it->source_location.get_java_bytecode_index())
            .second)
        {
          blocks_seen.insert(block_nr);
        }
        else
        {
          // clash, reset to search for a new one
          block_info.representative_inst = {};
          block_info.source_location = source_locationt::nil();
          msg.debug() << it->function << " block " << (block_nr + 1)
                      << ", location " << it->location_number
                      << ": bytecode-index "
                      << it->source_location.get_java_bytecode_index()
                      << " already instrumented."
                      << " Searching for alternative instruction"
                      << " to instrument." << messaget::eom;
        }
      }
    }
  }
}

void cover_basic_blockst::report_block_anomalies(
  const goto_programt &goto_program,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  std::set<unsigned> blocks_seen;
  forall_goto_program_instructions(it, goto_program)
  {
    const unsigned block_nr = block_of(it);
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
                    << it->location_number << " " << it->function
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

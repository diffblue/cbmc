/*******************************************************************\

Module: Basic Block Detection - Template Implementations

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Template implementations for basic block detection (see basic_blocks.h).
/// Extracted from goto-instrument/cover_basic_blocks.cpp.

#ifndef CPROVER_ANALYSES_BASIC_BLOCKS_IMPL_H
#define CPROVER_ANALYSES_BASIC_BLOCKS_IMPL_H

// ============================================================================
// Control-flow based detection (C/C++)
// ============================================================================

template <class P, class T, typename C>
std::optional<std::size_t>
basic_blocks_templatet<P, T, C>::continuation_of_block(
  T instruction,
  block_mapt &block_map)
{
  if(instruction->incoming_edges.size() != 1)
    return {};

  const auto in_t = *instruction->incoming_edges.cbegin();
  if(
    in_t->is_goto() && !in_t->is_backwards_goto() &&
    in_t->condition().is_true())
  {
    const auto it = block_map.find(in_t);
    if(it != block_map.end())
      return it->second;
  }

  return {};
}

template <class P, class T, typename C>
void basic_blocks_templatet<P, T, C>::compute(
  const P &program,
  const basic_block_configt &config)
{
  block_map.clear();
  this->block_infos.clear();

  bool next_is_target = true;
  const typename P::instructiont *preceding_assume = nullptr;
  std::size_t current_block = 0;

  forall_goto_program_instructions(it, program)
  {
    // When assume_delimit_blocks is set, an assume instruction terminates a
    // block (subsequent instructions may be unreachable). Multiple consecutive
    // assume instructions that share a source line are kept in the same block,
    // since a single program location may carry several assumptions (e.g.
    // emitted by an instrumentation pass).
    bool end_of_assume_group = false;
    if(config.assume_delimit_blocks)
    {
      end_of_assume_group =
        preceding_assume &&
        !(it->is_assume() &&
          same_source_line(
            preceding_assume->source_location(), it->source_location()));
    }

    // Is it a potential beginning of a block?
    if(next_is_target || it->is_target() || end_of_assume_group)
    {
      if(auto block_number = continuation_of_block(it, block_map))
      {
        current_block = *block_number;
      }
      else
      {
        this->block_infos.emplace_back();
        this->block_infos.back().representative_inst = it;
        this->block_infos.back().source_location = source_locationt::nil();
        current_block = this->block_infos.size() - 1;
      }
    }

    INVARIANT(
      current_block < this->block_infos.size(),
      "current block number out of range");
    block_infot &block_info = this->block_infos.at(current_block);

    block_map[it] = current_block;

    // Set representative program location to instrument
    if(
      !it->source_location().is_nil() &&
      !it->source_location().get_file().empty() &&
      !it->source_location().get_line().empty() &&
      !it->source_location().is_built_in() &&
      block_info.source_location.is_nil())
    {
      block_info.representative_inst = it; // update
      block_info.source_location = it->source_location();
    }

    next_is_target = it->is_goto() || it->is_function_call();

    if(config.assume_delimit_blocks)
      preceding_assume = it->is_assume() ? &*it : nullptr;
  }
}

// ============================================================================
// Bytecode-index based detection (Java)
// ============================================================================

template <class P, class T>
void java_basic_blocks_templatet<P, T>::compute(const P &program)
{
  this->block_infos.clear();
  index_to_block.clear();

  forall_goto_program_instructions(it, program)
  {
    const auto &location = it->source_location();
    const auto &bytecode_index = location.get_java_bytecode_index();
    auto entry =
      index_to_block.emplace(bytecode_index, this->block_infos.size());
    if(entry.second)
    {
      this->block_infos.emplace_back();
      this->block_infos.back().representative_inst = it;
      this->block_infos.back().source_location = location;
    }
  }
}

#endif // CPROVER_ANALYSES_BASIC_BLOCKS_IMPL_H

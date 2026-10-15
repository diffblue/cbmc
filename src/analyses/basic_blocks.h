/*******************************************************************\

Module: Basic Block Detection for Goto Programs

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Generic basic block detection for goto programs.
///
/// Extracted from goto-instrument/cover_basic_blocks.{cpp,h} so the analysis
/// can be reused outside coverage instrumentation. Two detection strategies
/// are provided as separate compile-time analyses, mirroring the template-only
/// style of natural_loops_templatet (no runtime/virtual dispatch):
///   - basic_blocks_templatet: control-flow based detection (C/C++);
///   - java_basic_blocks_templatet: bytecode-index based detection (Java).

#ifndef CPROVER_ANALYSES_BASIC_BLOCKS_H
#define CPROVER_ANALYSES_BASIC_BLOCKS_H

#include <util/invariant.h>
#include <util/irep.h>
#include <util/source_location.h>

#include <goto-programs/goto_program.h>

#include <map>
#include <optional>
#include <unordered_map>
#include <vector>

/// Options controlling basic block detection.
struct basic_block_configt
{
  /// If true, an assume instruction terminates a basic block (subsequent
  /// instructions may be unreachable). Consecutive assume instructions that
  /// share a source line are kept in the same block, since a single program
  /// location may carry several assumptions (e.g. emitted by an instrumentation
  /// pass).
  bool assume_delimit_blocks = true;

  basic_block_configt() = default;
  explicit basic_block_configt(bool _assume_delimit_blocks)
    : assume_delimit_blocks(_assume_delimit_blocks)
  {
  }
};

/// Storage and accessors shared by the basic block analyses. The detection
/// strategy (compute and block_of) is supplied by the derived analysis; the
/// concrete analysis is selected at compile time, so there is no virtual
/// dispatch.
template <class T>
class basic_blocks_baset
{
public:
  /// Information about a single basic block.
  struct block_infot
  {
    /// Instruction representative of this block (for instrumentation).
    std::optional<T> representative_inst;
    /// Source location representative of this block.
    source_locationt source_location;
  };

  /// \return the representative instruction of block \p block_nr, if any.
  std::optional<T> instruction_of(std::size_t block_nr) const
  {
    INVARIANT(block_nr < block_infos.size(), "block number out of range");
    return block_infos[block_nr].representative_inst;
  }

  /// \return the representative source location of block \p block_nr.
  const source_locationt &source_location_of(std::size_t block_nr) const
  {
    INVARIANT(block_nr < block_infos.size(), "block number out of range");
    return block_infos[block_nr].source_location;
  }

  /// \return the number of detected blocks.
  std::size_t size() const
  {
    return block_infos.size();
  }

protected:
  ~basic_blocks_baset() = default;

  /// Information about each block, indexed by block number.
  std::vector<block_infot> block_infos;
};

/// Control-flow based basic block detection (C/C++).
///
/// \tparam P: program type (e.g. const goto_programt)
/// \tparam T: instruction iterator type
/// \tparam C: comparison functor ordering iterators
template <class P, class T, typename C>
class basic_blocks_templatet : public basic_blocks_baset<T>
{
public:
  using typename basic_blocks_baset<T>::block_infot;
  using block_mapt = std::map<T, std::size_t, C>;

  /// Detect the basic blocks of \p program.
  explicit basic_blocks_templatet(
    const P &program,
    const basic_block_configt &config = basic_block_configt())
  {
    compute(program, config);
  }

  /// \return the block number containing instruction \p t.
  std::size_t block_of(T t) const
  {
    const auto it = block_map.find(t);
    INVARIANT(it != block_map.end(), "instruction must be part of a block");
    return it->second;
  }

  /// \return the instruction-to-block-number map, ordered by instruction.
  const block_mapt &instruction_blocks() const
  {
    return block_map;
  }

protected:
  /// Map each instruction to its block number.
  block_mapt block_map;

  void compute(const P &program, const basic_block_configt &config);

  /// \return the block number this instruction continues, when it is reached
  ///   only via a single unconditional forward goto.
  static std::optional<std::size_t>
  continuation_of_block(T instruction, block_mapt &block_map);

  /// \return true iff \p a and \p b are on the same source line.
  static bool
  same_source_line(const source_locationt &a, const source_locationt &b)
  {
    return a.get_file() == b.get_file() && a.get_line() == b.get_line();
  }
};

/// Bytecode-index based basic block detection (Java).
///
/// \tparam P: program type (e.g. const goto_programt)
/// \tparam T: instruction iterator type
template <class P, class T>
class java_basic_blocks_templatet : public basic_blocks_baset<T>
{
public:
  using typename basic_blocks_baset<T>::block_infot;

  /// Detect the basic blocks of \p program.
  explicit java_basic_blocks_templatet(const P &program)
  {
    compute(program);
  }

  /// \return the block number containing instruction \p t.
  std::size_t block_of(T t) const
  {
    const auto &bytecode_index = t->source_location().get_java_bytecode_index();
    const auto it = index_to_block.find(bytecode_index);
    INVARIANT(
      it != index_to_block.end(), "instruction must be part of a block");
    return it->second;
  }

protected:
  /// Map each Java bytecode index to its block number.
  std::unordered_map<irep_idt, std::size_t> index_to_block;

  void compute(const P &program);
};

/// Basic block detection on const goto programs (C/C++).
using basic_blockst = basic_blocks_templatet<
  const goto_programt,
  goto_programt::const_targett,
  goto_programt::target_less_than>;

/// Basic block detection on const goto programs (Java).
using java_basic_blockst = java_basic_blocks_templatet<
  const goto_programt,
  goto_programt::const_targett>;

// Include template implementations
#include "basic_blocks_impl.h"

#endif // CPROVER_ANALYSES_BASIC_BLOCKS_H

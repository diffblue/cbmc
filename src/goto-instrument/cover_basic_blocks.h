/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Basic blocks detection for Coverage Instrumentation
///
/// This module provides an adapter layer between the generic basic block
/// detection utility in src/analyses/basic_blocks.h and the coverage
/// instrumentation system. It extends the basic block detection with
/// source line tracking needed for coverage reporting.

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H
#define CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H

#include <goto-programs/goto_program.h>

#include <analyses/basic_blocks.h>

#include "source_lines.h"

class message_handlert;

class cover_blocks_baset
{
public:
  virtual ~cover_blocks_baset() = default;
  /// \param t: a goto instruction
  /// \return the block number of the block that the given goto instruction is
  //    part of
  virtual std::size_t block_of(goto_programt::const_targett t) const = 0;

  /// \param block_nr: a block number
  /// \return the instruction selected for
  ///   instrumentation representative of the given block
  virtual std::optional<goto_programt::const_targett>
  instruction_of(std::size_t block_nr) const = 0;

  /// \param block_nr: a block number
  /// \return the source location selected for
  ///   instrumentation representative of the given block
  virtual const source_locationt &
  source_location_of(std::size_t block_nr) const = 0;

  /// \param block_nr: a block number
  /// \return the source lines of the given block
  virtual const source_linest &source_lines_of(std::size_t block_nr) const = 0;

  /// Outputs the list of blocks
  virtual void output(std::ostream &out) const = 0;

  /// Output warnings about ignored blocks
  /// \param function_id: name of \p goto_program
  /// \param goto_program: The goto program
  /// \param message_handler: The message handler
  virtual void report_block_anomalies(
    const irep_idt &function_id,
    const goto_programt &goto_program,
    message_handlert &message_handler)
  {
    // unused parameters
    (void)function_id;
    (void)goto_program;
    (void)message_handler;
  }
};

/// Default basic block detection for C/C++ with source line tracking
/// This adapter extends the generic basic_blockst with source line
/// information needed for coverage reporting.
class cover_basic_blockst final : public cover_blocks_baset
{
public:
  /// Create basic block detector for the given program
  /// \param goto_program: The program to analyze
  /// \param config: Configuration for block detection (optional)
  explicit cover_basic_blockst(
    const goto_programt &goto_program,
    const basic_block_configt &config = basic_block_configt());

  /// \param t: a goto instruction
  /// \return the block number of the block
  ///         the given goto instruction is part of
  std::size_t block_of(goto_programt::const_targett t) const override;

  /// \param block_nr: a block number
  /// \return the instruction selected for
  ///   instrumentation representative of the given block
  std::optional<goto_programt::const_targett>
  instruction_of(std::size_t block_nr) const override;

  /// \param block_nr: a block number
  /// \return the source location selected for
  ///   instrumentation representative of the given block
  const source_locationt &
  source_location_of(std::size_t block_nr) const override;

  /// \param block_nr: a block number
  /// \return the source lines of the given block
  const source_linest &source_lines_of(std::size_t block_nr) const override;

  /// Output warnings about ignored blocks
  /// \param function_id: name of \p goto_program
  /// \param goto_program: The goto program
  /// \param message_handler: The message handler
  void report_block_anomalies(
    const irep_idt &function_id,
    const goto_programt &goto_program,
    message_handlert &message_handler) override;

  /// Outputs the list of blocks
  void output(std::ostream &out) const override;

private:
  /// The underlying basic block detector
  basic_blockst blocks;

  /// Extended block information with source lines
  struct block_infot
  {
    /// the set of source code lines belonging to this block
    source_linest source_lines;
  };

  /// Extended information for each block
  std::vector<block_infot> block_infos;

  /// Adds the lines which \p instruction spans to \p block.
  static void add_block_lines(
    block_infot &block,
    const goto_programt::instructiont &instruction);
};

/// Java-specific basic block detection with source line tracking
class cover_basic_blocks_javat final : public cover_blocks_baset
{
public:
  /// Create basic block detector for Java programs
  /// \param goto_program: The program to analyze
  explicit cover_basic_blocks_javat(const goto_programt &goto_program);

  /// \param t: a goto instruction
  /// \return block number the given goto instruction is part of
  std::size_t block_of(goto_programt::const_targett t) const override;

  /// \param block_number: a block number
  /// \return first instruction of the given block
  std::optional<goto_programt::const_targett>
  instruction_of(std::size_t block_number) const override;

  /// \param block_number: a block number
  /// \return source location corresponding to the given block
  const source_locationt &
  source_location_of(std::size_t block_number) const override;

  /// \param block_number: a block number
  /// \return the source lines of the given block
  const source_linest &source_lines_of(std::size_t block_number) const override;

  /// Outputs the list of blocks
  void output(std::ostream &out) const override;

private:
  /// The underlying Java basic block detector
  java_basic_blockst blocks;

  /// Source lines for each block
  std::vector<source_linest> block_source_lines;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H

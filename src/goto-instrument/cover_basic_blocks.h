/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Basic blocks detection for Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H
#define CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H

#include <unordered_set>

#include <util/message.h>

#include <goto-programs/goto_model.h>

class cover_blocks_baset
{
public:
  virtual ~cover_blocks_baset() = default;
  /// \param t: a goto instruction
  /// \return the block number of the block
  ///         the given goto instruction is part of
  virtual std::size_t block_of(goto_programt::const_targett t) const = 0;

  /// \param block_nr: a block number
  /// \return the instruction selected for
  ///   instrumentation representative of the given block
  virtual optionalt<goto_programt::const_targett>
  instruction_of(std::size_t block_nr) const = 0;

  /// \param block_nr: a block number
  /// \return the source location selected for
  ///   instrumentation representative of the given block
  virtual const source_locationt &
  source_location_of(std::size_t block_nr) const = 0;

  /// Outputs the list of blocks
  virtual void output(std::ostream &out) const = 0;

  /// Output warnings about ignored blocks
  /// \param goto_program: The goto program
  /// \param message_handler: The message handler
  virtual void report_block_anomalies(
    const goto_programt &goto_program,
    message_handlert &message_handler)
  {
    // unused parameters
    (void)goto_program;
    (void)message_handler;
  }
};

class cover_basic_blockst final : public cover_blocks_baset
{
public:
  explicit cover_basic_blockst(const goto_programt &_goto_program);

  /// \param t: a goto instruction
  /// \return the block number of the block
  ///         the given goto instruction is part of
  std::size_t block_of(goto_programt::const_targett t) const override;

  /// \param block_nr: a block number
  /// \return the instruction selected for
  ///   instrumentation representative of the given block
  optionalt<goto_programt::const_targett>
  instruction_of(std::size_t block_nr) const override;

  /// \param block_nr: a block number
  /// \return the source location selected for
  ///   instrumentation representative of the given block
  const source_locationt &
  source_location_of(std::size_t block_nr) const override;

  /// Output warnings about ignored blocks
  /// \param goto_program: The goto program
  /// \param message_handler: The message handler
  void report_block_anomalies(
    const goto_programt &goto_program,
    message_handlert &message_handler) override;

  /// Outputs the list of blocks
  void output(std::ostream &out) const override;

private:
  typedef std::map<goto_programt::const_targett, std::size_t> block_mapt;

  struct block_infot
  {
    /// the program location to instrument for this block
    optionalt<goto_programt::const_targett> representative_inst;

    /// the source location representative for this block
    /// (we need a separate copy of source locations because we attach
    ///  the line number ranges to them)
    source_locationt source_location;

    /// the set of lines belonging to this block
    std::unordered_set<std::size_t> lines;
  };

  /// map program locations to block numbers
  block_mapt block_map;
  /// map block numbers to block information
  std::vector<block_infot> block_infos;

  /// create list of covered lines as CSV string and set as property of source
  /// location of basic block, compress to ranges if applicable
  static void update_covered_lines(block_infot &block_info);

  /// If this block is a continuation of a previous block through unconditional
  /// forward gotos, return this blocks number.
  static optionalt<std::size_t> continuation_of_block(
    const goto_programt::const_targett &instruction,
    block_mapt &block_map);
};

class cover_basic_blocks_javat final : public cover_blocks_baset
{
private:
  // map block number to first instruction of the block
  std::vector<goto_programt::const_targett> block_infos;
  // map block number to its location
  std::vector<source_locationt> block_locations;
  // map java indexes to block indexes
  std::unordered_map<irep_idt, std::size_t> index_to_block;

public:
  explicit cover_basic_blocks_javat(const goto_programt &_goto_program);

  /// \param t: a goto instruction
  /// \return block number the given goto instruction is part of
  std::size_t block_of(goto_programt::const_targett t) const override;

  /// \param block_number: a block number
  /// \return first instruction of the given block
  optionalt<goto_programt::const_targett>
  instruction_of(std::size_t block_number) const override;

  /// \param block_number: a block number
  /// \return source location corresponding to the given block
  const source_locationt &
  source_location_of(std::size_t block_number) const override;

  /// Outputs the list of blocks
  void output(std::ostream &out) const override;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H

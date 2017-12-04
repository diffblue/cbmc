/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Basic blocks detection for Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H
#define CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H

#include <unordered_set>

#include <goto-programs/goto_model.h>

class message_handlert;

class cover_basic_blockst
{
public:
  explicit cover_basic_blockst(const goto_programt &_goto_program);

  /// \param t a goto instruction
  /// \return the block number of the block
  ///         the given goto instruction is part of
  unsigned block_of(goto_programt::const_targett t) const;

  /// \param block_nr a block number
  /// \return  the instruction selected for
  ///   instrumentation representative of the given block
  goto_programt::const_targett instruction_of(unsigned block_nr) const;

  /// \param block_nr a block number
  /// \return  the source location selected for
  ///   instrumentation representative of the given block
  const source_locationt &source_location_of(unsigned block_nr) const;

  /// Select an instruction to be instrumented for each basic block such that
  /// the java bytecode indices for each basic block is unique
  /// \param goto_program The goto program
  /// \param message_handler The message handler
  void select_unique_java_bytecode_indices(
    const goto_programt &goto_program,
    message_handlert &message_handler);

  /// Output warnings about ignored blocks
  /// \param goto_program The goto program
  /// \param message_handler The message handler
  void report_block_anomalies(
    const goto_programt &goto_program,
    message_handlert &message_handler);

  /// Outputs the list of blocks
  void output(std::ostream &out) const;

protected:
  // map program locations to block numbers
  typedef std::map<goto_programt::const_targett, unsigned> block_mapt;
  block_mapt block_map;

  struct block_infot
  {
    /// the program location to instrument for this block
    goto_programt::const_targett representative_inst;

    /// the source location representative for this block
    // (we need a separate copy of source locations because we attach
    //  the line number ranges to them)
    source_locationt source_location;

    // map block numbers to source code locations
    /// the set of lines belonging to this block
    std::unordered_set<unsigned> lines;
  };

  typedef std::vector<block_infot> block_infost;
  block_infost block_infos;

  /// create list of covered lines as CSV string and set as property of source
  /// location of basic block, compress to ranges if applicable
  void update_covered_lines(block_infot &block_info);
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H

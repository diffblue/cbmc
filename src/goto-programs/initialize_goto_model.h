/*******************************************************************\

Module: Initialize a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Initialize a Goto Program

#ifndef CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H

#include "goto_model.h"

class language_filest;
class message_handlert;
class optionst;

goto_modelt initialize_goto_model(
  const std::vector<std::string> &files,
  message_handlert &message_handler,
  const optionst &options);

/// Populate \p symbol_table from \p sources by parsing and type checking via
/// \p language_files. Throws exceptions if processing fails.
/// \param sources: Collection of input source files. No operation is performed
///   if the collection is empty.
/// \param options: Configuration options.
/// \param language_files: Language parsing and type checking facilities.
/// \param [out] symbol_table: Symbol table to be populated.
/// \param message_handler: Message handler.
void initialize_from_source_files(
  const std::list<std::string> &sources,
  const optionst &options,
  language_filest &language_files,
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

/// Process the "function" option in \p options to prepare a custom entry point
/// to replace \c __CPROVER_start.
/// \param language_files: Language parsing and type checking facilities.
/// \param symbol_table: Symbol table for mode lookup and removal of an existing
///   entry point.
/// \param unload: Functor to remove an existing entry point.
/// \param options: Configuration options.
/// \param try_mode_lookup: Try to infer the entry point's mode from the symbol
///   table.
/// \param message_handler: Message handler.
void set_up_custom_entry_point(
  language_filest &language_files,
  symbol_tablet &symbol_table,
  const std::function<void(const irep_idt &)> &unload,
  const optionst &options,
  bool try_mode_lookup,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H

/*******************************************************************\

Module: Interface for Goto Checkers to provide Fault Localization

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Interface for Goto Checkers to provide Fault Localization

#ifndef CPROVER_GOTO_CHECKER_FAULT_LOCALIZATION_PROVIDER_H
#define CPROVER_GOTO_CHECKER_FAULT_LOCALIZATION_PROVIDER_H

#include <map>

#include <goto-programs/goto_program.h>

class goto_tracet;
class namespacet;

struct fault_location_infot
{
  typedef std::map<goto_programt::const_targett, std::size_t> score_mapt;
  score_mapt scores;
};

/// An implementation of `incremental_goto_checkert`
/// may implement this interface to provide fault localization information.
class fault_localization_providert
{
public:
  /// Returns the most likely fault locations
  /// for the given FAILed \p property_id
  virtual fault_location_infot
  localize_fault(const irep_idt &property_id) const = 0;

  virtual ~fault_localization_providert() = default;
};

#endif // CPROVER_GOTO_CHECKER_FAULT_LOCALIZATION_PROVIDER_H

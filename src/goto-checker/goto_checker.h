/*******************************************************************\

Module: Goto Checker Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker Interface

#ifndef CPROVER_GOTO_CHECKER_GOTO_CHECKER_H
#define CPROVER_GOTO_CHECKER_GOTO_CHECKER_H

#include <goto-programs/goto_trace.h>

#include <util/options.h>
#include <util/ui_message.h>

#include "properties.h"

/// An implementation of `goto_checkert` provides functionality for
/// checking a set of properties and returning counterexamples
/// one by one to the caller.
/// An implementation of `goto_checkert` is responsible for maintaining
/// the state of the analysis that it performs (e.g. goto-symex, solver, etc).
/// It is not responsible for maintaining outcomes (e.g. property results,
/// counterexamples, etc). However, an implementation may restrict the
/// sets of properties it is asked to check (e.g. only sequences of subsets).
class goto_checkert : public messaget
{
public:
  /// Check whether the given properties with status UNKNOWN or newly
  /// discovered properties hold
  /// \return The properties whose status has been determined
  /// If there is a property with status FAIL then its counterexample
  /// can be retrieved by calling `build_error_trace` before any
  /// subsequent call to operator().
  /// `goto_checkert` derivatives shall be implemented in a way such
  /// that repeated calls to operator() shall return the next FAILed
  /// property until eventually not returning any FAILing properties.
  virtual propertiest operator()(const propertiest &) = 0;

  /// This builds and returns the counterexample
  virtual goto_tracet build_error_trace() = 0;

protected:
  goto_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler);

  const optionst &options;
  ui_message_handlert &ui_message_handler;
};

#endif // CPROVER_GOTO_CHECKER_GOTO_CHECKER_H

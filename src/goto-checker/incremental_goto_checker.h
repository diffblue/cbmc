/*******************************************************************\

Module: Incremental Goto Checker Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Incremental Goto Checker Interface

#ifndef CPROVER_GOTO_CHECKER_INCREMENTAL_GOTO_CHECKER_H
#define CPROVER_GOTO_CHECKER_INCREMENTAL_GOTO_CHECKER_H

#include <util/ui_message.h>

#include "properties.h"

class goto_tracet;
class optionst;

/// An implementation of `incremental_goto_checkert` provides functionality for
/// checking a set of properties and returning counterexamples
/// one by one to the caller.
/// An implementation of `incremental_goto_checkert` is responsible for
/// maintaining the state of the analysis that it performs (e.g. goto-symex,
/// solver, etc).
/// An implementation of `incremental_goto_checkert` is not responsible for
/// maintaining outcomes (e.g. property status, counterexamples, etc).
/// However, an implementation may restrict the sets of properties it is asked
/// to check on repeated invocations of its operator (e.g. only sequences of
/// subsets of properties) to optimize the incremental algorithm it uses.
class incremental_goto_checkert
{
public:
  incremental_goto_checkert() = delete;
  incremental_goto_checkert(const incremental_goto_checkert &) = delete;
  virtual ~incremental_goto_checkert() = default;

  enum class resultt
  {
    /// The goto checker may be able to find another FAILed property
    /// if operator() is called again.
    FOUND_FAIL,
    /// The goto checker has returned all results for the given set
    /// of properties.
    DONE
  };

  /// Check whether the given properties with status NOT_CHECKED, UNKNOWN or
  /// properties newly discovered by `goto_checkert` hold.
  /// \param [out] properties: Properties updated to whether their status
  ///   have been determined. Newly discovered properties are added.
  /// \return whether the goto checker found a violated property (FOUND_FAIL) or
  ///   whether it is DONE with the given properties.
  /// After returning DONE, another call to operator() with the same
  /// properties will return DONE and leave the properties' status unchanged.
  /// If there is a property with status FAIL then its counterexample
  /// can be retrieved by calling `build_error_trace` before any
  /// subsequent call to operator().
  /// `goto_checkert` derivatives shall be implemented in a way such
  /// that repeated calls to operator() shall return when the next FAILed
  /// property has been found until eventually it does not find any
  /// failing properties any more.
  virtual resultt operator()(propertiest &properties) = 0;

  /// Builds and returns the counterexample
  virtual goto_tracet build_error_trace() const = 0;

  // Outputs an error witness in GraphML format (see `graphml_witnesst`)
  virtual void output_error_witness(const goto_tracet &) = 0;

  // Outputs a proof in GraphML format (see `graphml_witnesst`)
  virtual void output_proof() = 0;

protected:
  incremental_goto_checkert(const optionst &, ui_message_handlert &);

  const optionst &options;
  ui_message_handlert &ui_message_handler;
  messaget log;
};

#endif // CPROVER_GOTO_CHECKER_INCREMENTAL_GOTO_CHECKER_H

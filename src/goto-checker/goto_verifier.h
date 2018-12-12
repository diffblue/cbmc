/*******************************************************************\

Module: Goto Verifier Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier Interface

#ifndef CPROVER_GOTO_CHECKER_GOTO_VERIFIER_H
#define CPROVER_GOTO_CHECKER_GOTO_VERIFIER_H

#include <util/optional.h>
#include <util/options.h>
#include <util/ui_message.h>

#include "properties.h"

/// An implementation of `goto_verifiert` checks all properties in
/// a goto model. It typically uses, but doesn't have to use, an
/// `incremental_goto_checkert` to iteratively determine the verification status
/// of each property.
class goto_verifiert
{
public:
  goto_verifiert() = delete;
  goto_verifiert(const goto_verifiert &) = delete;
  virtual ~goto_verifiert() = default;

  /// Check whether all properties hold.
  /// \return PASS if all properties are PASS,
  ///         FAIL if at least one property is FAIL and no property is ERROR,
  ///         UNKNOWN if no property is FAIL or ERROR and
  ///           at least one property is UNKNOWN,
  ///         ERROR if at least one property is error.
  virtual resultt operator()() = 0;

  /// Report results
  virtual void report() = 0;

  /// Returns the properties
  const propertiest &get_properties()
  {
    return properties;
  }

protected:
  goto_verifiert(const optionst &, ui_message_handlert &);

  const optionst &options;
  ui_message_handlert &ui_message_handler;
  messaget log;
  propertiest properties;
};

#endif // CPROVER_GOTO_CHECKER_GOTO_VERIFIER_H

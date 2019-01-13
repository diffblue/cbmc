/*******************************************************************\

Module: Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Properties

#ifndef CPROVER_GOTO_CHECKER_PROPERTIES_H
#define CPROVER_GOTO_CHECKER_PROPERTIES_H

#include <unordered_map>

#include <goto-programs/goto_model.h>

/// The status of a property
enum class property_statust
{
  /// The property was not checked (also used for initialization)
  NOT_CHECKED,
  /// The checker was unable to determine the status of the property
  UNKNOWN,
  /// The property was proven to be unreachable
  NOT_REACHABLE,
  /// The property was not violated
  PASS,
  /// The property was violated
  FAIL,
  /// An error occurred during goto checking
  ERROR
};

std::string as_string(property_statust);

/// The result of goto verifying
enum class resultt
{
  /// No property was violated, neither was there an error
  UNKNOWN,
  /// No properties were violated
  PASS,
  /// Some properties were violated
  FAIL,
  /// An error occurred during goto checking
  ERROR
};

std::string as_string(resultt);

struct property_infot
{
  property_infot(
    goto_programt::const_targett pc,
    std::string description,
    property_statust status);

  /// A pointer to the corresponding goto instruction
  goto_programt::const_targett pc;

  /// A description (usually derived from the assertion's comment)
  std::string description;

  /// The status of the property
  property_statust status;
};

/// A map of property IDs to property infos
typedef std::unordered_map<irep_idt, property_infot> propertiest;

/// Returns the properties in the goto model
propertiest initialize_properties(const abstract_goto_modelt &);

#endif // CPROVER_GOTO_CHECKER_PROPERTIES_H

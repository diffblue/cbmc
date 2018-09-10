/*******************************************************************\

Module: Goto Checker Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Property Map

#ifndef CPROVER_GOTO_CHECKER_PROPERTIES_H
#define CPROVER_GOTO_CHECKER_PROPERTIES_H

#include <unordered_map>

#include <goto-programs/goto_model.h>

/// The result status of a property, or
/// The result of goto checking and verifying
enum class resultt
{
  /// The property was not violated, or
  /// No properties were violated
  PASS,
  /// The property was violated, or
  /// Some properties were violated
  FAIL,
  /// An error occurred during goto checking
  ERROR,
  /// The status of the property is unknown, or
  /// No property was violated, neither was there an error
  UNKNOWN
};

std::string as_string(resultt);

struct property_infot
{
  resultt result;
  goto_programt::const_targett location;
};

/// the irep_idt is the property id
typedef std::unordered_map<irep_idt, property_infot> propertiest;

propertiest initialize_properties(const goto_modelt &);

resultt &operator|=(resultt &, resultt const &);
resultt &operator&=(resultt &, resultt const &);

resultt determine_result(const propertiest &properties);

void merge_properties(
  propertiest &properties,
  const propertiest &updated_properties);

#endif // CPROVER_GOTO_CHECKER_PROPERTIES_H

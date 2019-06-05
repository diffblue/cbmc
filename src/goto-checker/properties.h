/*******************************************************************\

Module: Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Properties

#ifndef CPROVER_GOTO_CHECKER_PROPERTIES_H
#define CPROVER_GOTO_CHECKER_PROPERTIES_H

#include <list>
#include <string>
#include <unordered_map>

#include <goto-programs/goto_model.h>

class json_objectt;
class json_stream_objectt;
class xmlt;

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

/// Updates \p properties with the assertions in \p goto_model
void update_properties_from_goto_model(
  propertiest &properties,
  const abstract_goto_modelt &goto_model);

std::string
as_string(const irep_idt &property_id, const property_infot &property_info);

xmlt xml(const irep_idt &property_id, const property_infot &property_info);

json_objectt
json(const irep_idt &property_id, const property_infot &property_info);

/// Write the property info into the given JSON stream object
void json(json_stream_objectt &, const irep_idt &, const property_infot &);

int result_to_exit_code(resultt result);

/// Return the number of properties with given \p status
std::size_t count_properties(const propertiest &, property_statust);

/// Return true if the status is NOT_CHECKED or UNKNOWN
bool is_property_to_check(property_statust);

/// Return true if there as a property with NOT_CHECKED or UNKNOWN status
bool has_properties_to_check(const propertiest &properties);

property_statust &operator|=(property_statust &, property_statust const &);
property_statust &operator&=(property_statust &, property_statust const &);
resultt determine_result(const propertiest &properties);

/// Store information about assumptions made while performing verification.
struct assumption_infot
{
  assumption_infot(
    goto_programt::const_targett pc,
    std::string description) :
    pc(pc),
    description(description)
  {
  }

  /// A pointer to the corresponding goto instruction
  goto_programt::const_targett pc;

  /// A description (possibly derived from the assumption's comment)
  std::string description;
};

/// A collection of assumptions
typedef std::list<assumption_infot> assumptionst;

std::string
as_string(const assumption_infot &property_info);

xmlt xml(const assumption_infot &property_info);

json_objectt
json(const assumption_infot &property_info);

#endif // CPROVER_GOTO_CHECKER_PROPERTIES_H

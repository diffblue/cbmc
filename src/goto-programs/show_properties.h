/*******************************************************************\

Module: Show the properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show the properties

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H
#define CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H

#include <util/ui_message.h>
#include <util/optional.h>

class namespacet;
class goto_modelt;
class symbol_tablet;
class goto_programt;
class goto_functionst;
class message_handlert;

// clang-format off
#define OPT_SHOW_PROPERTIES \
  "(show-properties)"

#define HELP_SHOW_PROPERTIES \
  " --show-properties            show the properties, but don't run analysis\n" // NOLINT(*)
// clang-format on

void show_properties(
  const goto_modelt &,
  message_handlert &message_handler,
  ui_message_handlert::uit ui);

void show_properties(
  const namespacet &ns,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

/// \brief Returns a source_locationt that corresponds
/// to the property given by an irep_idt.
/// \param property: irep_idt that identifies property
/// \param goto_functions:  program in which to search for
///   the property
/// \return optional<source_locationt> the location of the
/// property, if found.
optionalt<source_locationt> find_property(
    const irep_idt &property,
    const goto_functionst &goto_functions);

/// \brief Collects the properties in the goto program into a `json_arrayt`
/// \param json_properties: JSON array to hold the properties
/// \param ns: namespace
/// \param identifier: function id of the goto program
/// \param goto_program: the goto program
void convert_properties_json(
  json_arrayt &json_properties,
  const namespacet &ns,
  const irep_idt &identifier,
  const goto_programt &goto_program);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H

/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H
#define CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H

#include <goto-checker/properties.h>

#include <iosfwd>

#include <analyses/ai_history.h>

class abstract_goto_modelt;
class ai_baset;
class goto_modelt;
class message_handlert;
class optionst;

bool static_verifier(
  const goto_modelt &,
  const ai_baset &,
  const optionst &,
  message_handlert &,
  std::ostream &);

/// Use the information from the abstract interpreter to fill out the statuses
/// of the passed properties
/// \param abstract_goto_model The goto program to verify
/// \param ai The abstract interpreter (should be run to fixpoint
///           before calling this function)
/// \param properties The properties to fill out
void static_verifier(
  const abstract_goto_modelt &abstract_goto_model,
  const ai_baset &ai,
  propertiest &properties);

/// An ai_baset contains zero or more histories that reach a location.
/// In a given history, a Boolean expression can be true, false or unknown.
/// If we only care about "does there exist a history that make the condition
/// true/false/unknown" then that means there are 8 possible statuses.
/// In practice not all of them are usefully distinguishable, so we only
/// consider 4 of them.
/// Also note that because abstract interpretation is an over-approximate
/// analysis, the existence of a history does not necessarily mean that there
/// is an actual executation trace that makes the condition true/false.
enum class ai_verifier_statust
{
  TRUE,               // true : 1+, unknown :  0, false :  0
  FALSE_IF_REACHABLE, // true : 0+, unknown :  0, false : 1+
  NOT_REACHABLE,      // true :  0, unknown :  0, false :  0
  UNKNOWN             // true : 0+, unknown : 1+, false : 0+
};

std::string as_string(const ai_verifier_statust &);

/// The result of verifying a single assertion
/// As well as the status of the assertion (see above), it also contains the
/// location (source_location and function_id) and the set of histories
/// in which the assertion is unknown or false, so that more detailed
/// post-processing or error output can be done.
class static_verifier_resultt
{
public:
  ai_verifier_statust status;
  source_locationt source_location;
  irep_idt function_id;
  ai_history_baset::trace_sett unknown_histories;
  ai_history_baset::trace_sett false_histories;

  static_verifier_resultt(
    const ai_baset &ai,
    goto_programt::const_targett assert_location,
    irep_idt func_id,
    const namespacet &ns);

  jsont output_json(void) const;
  xmlt output_xml(void) const;
};

#endif // CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H

/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H
#define CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H

#include <analyses/ai.h>
#include <goto-checker/properties.h>

#include <iosfwd>

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

enum class ai_verifier_statust
{
  TRUE,
  FALSE_IF_REACHABLE,
  NOT_REACHABLE,
  UNKNOWN
};

std::string as_string(const ai_verifier_statust &);

/// The result of verifying a single assertion
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

/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H
#define CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H

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

#endif // CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H

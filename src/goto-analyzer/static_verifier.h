/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H
#define CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H

#include <iosfwd>

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

#endif // CPROVER_GOTO_ANALYZER_STATIC_VERIFIER_H

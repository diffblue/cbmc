/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_SHOW_DOMAIN_H
#define CPROVER_GOTO_ANALYZER_STATIC_SHOW_DOMAIN_H

#include <iosfwd>

class ai_baset;
class goto_modelt;
class message_handlert;
class optionst;

void static_show_domain(
  const goto_modelt &,
  const ai_baset &,
  const optionst &,
  std::ostream &);

#endif // CPROVER_GOTO_ANALYZER_STATIC_SHOW_DOMAIN_H

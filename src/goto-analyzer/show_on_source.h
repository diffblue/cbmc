/*******************************************************************\

Module: goto-analyzer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_SHOW_ON_SOURCE_H
#define CPROVER_GOTO_ANALYZER_SHOW_ON_SOURCE_H

class ai_baset;
class goto_modelt;
class message_handlert;

void show_on_source(const goto_modelt &, const ai_baset &, message_handlert &);

#endif // CPROVER_GOTO_ANALYZER_SHOW_ON_SOURCE_H

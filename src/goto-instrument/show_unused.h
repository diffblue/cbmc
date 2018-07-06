/*******************************************************************\

Module: Show unused variables (including write only)

Author: Norbert Manthey nmanthey@amazon.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_SHOW_UNUSED_H
#define CPROVER_GOTO_INSTRUMENT_SHOW_UNUSED_H

#include <util/ui_message.h>

#include <goto-programs/goto_model.h>

class symbol_tablet;

/** display all variables that are never read in the program */
bool show_unused(ui_message_handlert::uit ui, const goto_modelt &goto_model);

#endif

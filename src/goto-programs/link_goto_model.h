/*******************************************************************\

Module: Read Goto Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Read Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_LINK_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_LINK_GOTO_MODEL_H

class goto_modelt;
class message_handlert;

void link_goto_model(
  goto_modelt &dest,
  goto_modelt &src,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_LINK_GOTO_MODEL_H

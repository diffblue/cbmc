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
class replace_symbolt;

void link_goto_model(
  goto_modelt &dest,
  goto_modelt &src,
  unchecked_replace_symbolt &object_type_updates,
  message_handlert &);

void finalize_linking(
  goto_modelt &dest,
  const replace_symbolt &object_type_updates);

#endif // CPROVER_GOTO_PROGRAMS_LINK_GOTO_MODEL_H

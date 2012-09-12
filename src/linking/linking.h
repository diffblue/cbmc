/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LINKING_H
#define CPROVER_LINKING_H

#include <message.h>
#include <context.h>

// this merges the context "new_context" into "dest_context",
// applying appropriate renamings to symbols in "new_context"
// when necessary

bool linking(
  contextt &dest_context,
  contextt &new_context,
  message_handlert &message_handler);

#endif

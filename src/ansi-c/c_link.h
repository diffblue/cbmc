/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_LINK_H
#define CPROVER_C_LINK_H

#include <message.h>
#include <context.h>

// this merges the context "new_context" into "dest_context",
// applying appropriate renamings to symbols in "new_context"
// when necessary

bool c_link(
  contextt &dest_context,
  contextt &new_context,
  message_handlert &message_handler);

#endif

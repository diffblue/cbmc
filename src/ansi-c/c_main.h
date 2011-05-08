/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_MAIN_H
#define CPROVER_C_MAIN_H

#include <context.h>
#include <message.h>
#include <std_code.h>

bool c_main(
  contextt &context,
  const std::string &default_prefix,
  const std::string &standard_main,
  message_handlert &message_handler);

void static_lifetime_init(
  contextt &context,
  const locationt &location);

#endif

/*******************************************************************\

Module: (naive) Fence insertion

Purpose: fences all the shared or volatile-declared variables

Author: Vincent Nimal

\*******************************************************************/

/// \file
/// (naive) Fence insertion

#ifndef CPROVER_MUSKETEER_FENCE_SHARED_H
#define CPROVER_MUSKETEER_FENCE_SHARED_H

class value_setst;
class goto_modelt;
class message_handlert;

/* finds all the shared variables (including static, global and dynamic) */
void fence_all_shared(
  message_handlert &,
  value_setst &,
  goto_modelt &);

/* finds all the shared variables (including static, global and dynamic) */
void fence_all_shared_aeg(
  message_handlert &,
  value_setst &,
  goto_modelt &);

/* finds all the volatile-declared variables */
void fence_volatile(
  message_handlert &,
  value_setst &,
  goto_modelt &);

#endif // CPROVER_MUSKETEER_FENCE_SHARED_H

/*******************************************************************\

Module: Show the goto functions as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show the goto cfg, where nodes are colored based on a
/// "proof complexity" weight mechanism.

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_GOTO_PROOF_CFG_H
#define CPROVER_GOTO_PROGRAMS_SHOW_GOTO_PROOF_CFG_H

class namespacet;
class goto_modelt;
class goto_functionst;
class ui_message_handlert;

// clang-format off
#define OPT_SHOW_GOTO_PROOF_CFG \
  "(show-goto-proof-cfg)"

#define HELP_SHOW_GOTO_PROOF_CFG \
  " --show-goto-proof-cfg        show goto cfg with nodes colored with proof complexity\n"
// clang-format on

void show_goto_proof_cfg(
  const namespacet &ns,
  ui_message_handlert &ui_message_handler,
  const goto_functionst &goto_functions);

void show_goto_proof_cfg(
  const goto_modelt &, 
  ui_message_handlert &ui_message_handler);


#endif // CPROVER_GOTO_PROGRAMS_SHOW_GOTO_PROOF_CFG_H

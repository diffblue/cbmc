/*******************************************************************\

Module: Show the goto functions as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show the goto cfg, where nodes are colored based on a
/// "proof complexity" weight mechanism.

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_GOTO_PROOF_CFG_H
#define CPROVER_GOTO_PROGRAMS_SHOW_GOTO_PROOF_CFG_H

#include <list>
#include <string>
#include <set>
#include <map>
#include "goto_program.h"
#include "proof_cfg_metrics.h"

class namespacet;
class abstract_goto_modelt;
class goto_functionst;
class ui_message_handlert;

#include <goto-symex/solver_hardness.h>

// clang-format off
#define OPT_SHOW_GOTO_PROOF_CFG \
  "(show-goto-proof-cfg):" \
  "(show-goto-proof-cfg)"

#define HELP_SHOW_GOTO_PROOF_CFG \
  " --show-goto-proof-cfg        show goto cfg with nodes colored with proof complexity\n"
// clang-format on


void show_goto_proof_cfg(
  const namespacet &ns,
  ui_message_handlert &ui_message_handler,
  const std::list<std::string> roots,
  const goto_functionst &goto_functions,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info);

void show_goto_proof_cfg(
  const abstract_goto_modelt &, 
  const std::list<std::string> roots,
  ui_message_handlert &ui_message_handler,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info);

void compute_instruction_sat_hardness (std::map<goto_programt::const_targett, sat_infot> instr_sat_info,
                                       const solver_hardnesst &solver_hardness);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_GOTO_PROOF_CFG_H

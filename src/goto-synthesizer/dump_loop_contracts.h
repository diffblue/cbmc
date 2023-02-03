/*******************************************************************\

Module: Dump Loop Contracts as JSON

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

/// \file
/// Dump Loop Contracts as JSON

#ifndef CPROVER_GOTO_SYNTHESIZER_DUMP_LOOP_CONTRACTS_H
#define CPROVER_GOTO_SYNTHESIZER_DUMP_LOOP_CONTRACTS_H

#include "synthesizer_utils.h"

#include <iosfwd>
#include <string>

void dump_loop_contracts(
  goto_modelt &goto_model,
  const std::map<loop_idt, exprt> &invariant_map,
  const std::map<loop_idt, std::set<exprt>> &assigns_map,
  const std::string &json_output_str,
  std::ostream &out);

#define OPT_DUMP_LOOP_CONTRACTS "(json-output):(dump-loop-contracts)"

// clang-format off
#define HELP_DUMP_LOOP_CONTRACTS \
    " --dump-loop-contracts         dump synthesized loop contracts as JSON\n" /* NOLINT(whitespace/line_length) */ \
    " --json-output <file>          specify the output destination of the dumped loop contracts\n" // NOLINT(*)

// clang-format on

#endif // CPROVER_GOTO_SYNTHESIZER_DUMP_LOOP_CONTRACTS_H

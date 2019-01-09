/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#ifndef CPROVER_GOTO_CHECKER_BMC_UTIL_H
#define CPROVER_GOTO_CHECKER_BMC_UTIL_H

#include <memory>

#include <goto-programs/safety_checker.h>

class goto_tracet;
class memory_model_baset;
class message_handlert;
class namespacet;
class optionst;
class prop_convt;
class symex_bmct;
class symex_target_equationt;
struct trace_optionst;
class ui_message_handlert;

void convert_symex_target_equation(
  symex_target_equationt &,
  prop_convt &,
  message_handlert &);

void report_failure(ui_message_handlert &);
void report_success(ui_message_handlert &);

void build_error_trace(
  goto_tracet &,
  const namespacet &,
  const symex_target_equationt &,
  const prop_convt &,
  ui_message_handlert &);

void output_error_trace(
  const goto_tracet &,
  const namespacet &,
  const trace_optionst &,
  ui_message_handlert &);

void output_graphml(const goto_tracet &, const namespacet &, const optionst &);
void output_graphml(
  const symex_target_equationt &,
  const namespacet &,
  const optionst &);

std::unique_ptr<memory_model_baset>
get_memory_model(const optionst &options, const namespacet &);

void setup_symex(
  symex_bmct &,
  const namespacet &,
  const optionst &,
  ui_message_handlert &);

void slice(
  symex_bmct &,
  symex_target_equationt &symex_target_equation,
  const namespacet &,
  const optionst &,
  ui_message_handlert &);

// clang-format off
#define OPT_BMC \
  "(program-only)" \
  "(show-loops)" \
  "(show-vcc)" \
  "(slice-formula)" \
  "(unwinding-assertions)" \
  "(no-unwinding-assertions)" \
  "(no-pretty-names)" \
  "(no-self-loops-to-assumptions)" \
  "(partial-loops)" \
  "(paths):" \
  "(show-symex-strategies)" \
  "(depth):" \
  "(unwind):" \
  "(unwindset):" \
  "(graphml-witness):" \
  "(unwindset):"

#define HELP_BMC \
  " --paths [strategy]           explore paths one at a time\n" \
  " --show-symex-strategies      list strategies for use with --paths\n" \
  " --program-only               only show program expression\n" \
  " --show-loops                 show the loops in the program\n" \
  " --depth nr                   limit search depth\n" \
  " --unwind nr                  unwind nr times\n" \
  " --unwindset L:B,...          unwind loop L with a bound of B\n" \
  "                              (use --show-loops to get the loop IDs)\n" \
  " --show-vcc                   show the verification conditions\n" \
  " --slice-formula              remove assignments unrelated to property\n" \
  " --unwinding-assertions       generate unwinding assertions (cannot be\n" \
  "                              used with --cover or --partial-loops)\n" \
  " --partial-loops              permit paths with partial loops\n" \
  " --no-self-loops-to-assumptions\n" \
  "                              do not simplify while(1){} to assume(0)\n" \
  " --no-pretty-names            do not simplify identifiers\n" \
  " --graphml-witness filename   write the witness in GraphML format to filename\n" // NOLINT(*)
// clang-format on

#endif // CPROVER_GOTO_CHECKER_BMC_UTIL_H

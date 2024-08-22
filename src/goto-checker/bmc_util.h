/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#ifndef CPROVER_GOTO_CHECKER_BMC_UTIL_H
#define CPROVER_GOTO_CHECKER_BMC_UTIL_H

#include <goto-instrument/unwindset.h>
#include <goto-symex/build_goto_trace.h>

#include "incremental_goto_checker.h"
#include "properties.h"

#include <chrono> // IWYU pragma: keep
#include <memory>

class decision_proceduret;
class goto_symex_property_decidert;
class goto_tracet;
class memory_model_baset;
class namespacet;
class optionst;
class symex_bmct;
class symex_target_equationt;
struct trace_optionst;
class ui_message_handlert;

/// Returns a function that checks whether an SSA step is an assertion
/// with \p property_id. Usually used for `build_goto_trace`.
ssa_step_predicatet
ssa_step_matches_failing_property(const irep_idt &property_id);

/// Outputs a message that an error trace is being built
void message_building_error_trace(messaget &);

void build_error_trace(
  goto_tracet &,
  const namespacet &,
  const symex_target_equationt &,
  const decision_proceduret &,
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

/// Post process the equation
/// - add partial order constraints
/// - slice
/// - perform validation
void postprocess_equation(
  symex_bmct &symex,
  symex_target_equationt &equation,
  const optionst &options,
  const namespacet &ns,
  ui_message_handlert &ui_message_handler);

/// Output a coverage report as generated by \ref symex_coveraget
/// if \p cov_out is non-empty.
/// \param cov_out: file to write the report to; no report is generated
///   if this is empty
/// \param goto_model: goto model to build the coverage report for
/// \param symex: symbolic execution run to report coverage for
/// \param ui_message_handler: status/warning message handler
void output_coverage_report(
  const std::string &cov_out,
  const abstract_goto_modelt &goto_model,
  const symex_bmct &symex,
  ui_message_handlert &ui_message_handler);

/// Sets property status to PASS for properties whose
/// conditions are constant true in the \p equation.
/// \param [in,out] properties: The status is updated in this data structure
/// \param [in,out] updated_properties: The set of property IDs of
///   updated properties
/// \param equation: A equation generated by goto-symex
void update_properties_status_from_symex_target_equation(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties,
  const symex_target_equationt &equation);

/// Sets the property status of NOT_CHECKED properties to PASS.
/// \param [in,out] properties: The status is updated in this data structure
/// \param [in,out] updated_properties: The IDs of updated properties are
///   added here
/// Note: this should inspect the equation, but the equation doesn't have
///   any useful information at the moment.
void update_status_of_not_checked_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties);

/// Sets the property status of UNKNOWN properties to PASS.
/// \param [in,out] properties: The status is updated in this data structure
/// \param [in,out] updated_properties: The set of property IDs of
///   updated properties
/// Note: we currently declare everything PASS that is UNKNOWN at the
///   end of the model checking algorithm.
void update_status_of_unknown_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties);

/// Converts the equation and sets up the property decider,
/// but does not call solve.
/// \param [in,out] properties: Sets the status of properties to be checked to
///   UNKNOWN
/// \param [in,out] equation: The equation that will be converted
/// \param [in,out] property_decider: The property decider that we are going to
///   set up
/// \param [in,out] ui_message_handler: For logging
/// \return The runtime for converting the equation
std::chrono::duration<double> prepare_property_decider(
  propertiest &properties,
  symex_target_equationt &equation,
  goto_symex_property_decidert &property_decider,
  ui_message_handlert &ui_message_handler);

/// Runs the property decider to solve the equation
/// \param [in,out] result: For recording the progress and the updated
///   properties
/// \param [in,out] properties: The status will be updated
/// \param [in,out] property_decider: The property decider that will solve the
///   equation
/// \param [in,out] ui_message_handler: For logging
/// \param solver_runtime: The solver runtime will be added and output
/// \param set_pass: If true then update UNKNOWN properties to PASS
///   if the solver returns UNSATISFIABLE
void run_property_decider(
  incremental_goto_checkert::resultt &result,
  propertiest &properties,
  goto_symex_property_decidert &property_decider,
  ui_message_handlert &ui_message_handler,
  std::chrono::duration<double> solver_runtime,
  bool set_pass = true);

#define OPT_BMC                                                                \
  "(program-only)"                                                             \
  "(show-byte-ops)"                                                            \
  "(show-vcc)"                                                                 \
  "(show-goto-symex-steps)"                                                    \
  "(show-points-to-sets)"                                                      \
  "(slice-formula)"                                                            \
  "(unwinding-assertions)"                                                     \
  "(no-unwinding-assertions)"                                                  \
  "(no-self-loops-to-assumptions)"                                             \
  "(partial-loops)"                                                            \
  "(paths):"                                                                   \
  "(show-symex-strategies)"                                                    \
  "(depth):"                                                                   \
  "(max-field-sensitivity-array-size):"                                        \
  "(no-array-field-sensitivity)"                                               \
  "(graphml-witness):"                                                         \
  "(symex-complexity-limit):"                                                  \
  "(symex-complexity-failed-child-loops-limit):"                               \
  "(incremental-loop):"                                                        \
  "(unwind-min):"                                                              \
  "(unwind-max):"                                                              \
  "(ignore-properties-before-unwind-min)"                                      \
  "(symex-cache-dereferences)" OPT_UNWINDSET

#define HELP_BMC                                                               \
  " {y--paths} [strategy] \t explore paths one at a time\n"                    \
  " {y--show-symex-strategies} \t list strategies for use with {y--paths}\n"   \
  " {y--show-goto-symex-steps} \t show which steps symex travels, includes "   \
  "diagnostic information\n"                                                   \
  " {y--show-points-to-sets} \t show points-to sets for pointer dereference. " \
  "Requires {y--json-ui}.\n"                                                   \
  " {y--program-only} \t only show program expression\n"                       \
  " {y--show-byte-ops} \t show all byte extracts and updates\n"                \
  " {y--depth} {unr} \t limit search depth\n"                                  \
  " {y--max-field-sensitivity-array-size} {uM} \t "                            \
  "maximum size {uM} of arrays for which field sensitivity will be "           \
  "applied to array, the default is 64\n"                                      \
  " {y--no-array-field-sensitivity} \t "                                       \
  "deactivate field sensitivity for arrays, this is equivalent to setting "    \
  "the maximum field sensitivity size for arrays to 0\n" HELP_UNWINDSET        \
  " {y--incremental-loop} {uL} \t "                                            \
  "check properties after each unwinding of loop {uL} (use {y--show-loops} "   \
  "to get the loop IDs)\n"                                                     \
  " {y--unwind-min} {unr} \t "                                                 \
  "start incremental-loop after {unr} unwindings but before solving that "     \
  "iteration. If for example it is 1, then the loop will be unwound once, "    \
  "and immediately checked. Note: this means for {y--unwind-min} 1 or 0 all "  \
  "properties are checked.\n"                                                  \
  " {y--unwind-max} {unr} \t stop incremental-loop after {unr} unwindings\n"   \
  " {y--ignore-properties-before-unwind-min} \t "                              \
  "do not check properties before unwind-min when using "                      \
  "{y--incremental-loop}\n"                                                    \
  " {y--show-vcc} \t show the verification conditions\n"                       \
  " {y--slice-formula} \t remove assignments unrelated to property\n"          \
  " {y--unwinding-assertions} \t generate unwinding assertions (cannot be "    \
  "used with {y--cover})\n"                                                    \
  " {y--partial-loops} \t permit paths with partial loops\n"                   \
  " {y--no-self-loops-to-assumptions} \t do not simplify while(1){ {}} to "    \
  "assume(0)\n"                                                                \
  " {y--symex-complexity-limit} {uN} \t "                                      \
  "how complex ({uN}) a path can become before symex abandons it. Currently "  \
  "uses guard size to calculate complexity.\n"                                 \
  " {y--symex-complexity-failed-child-loops-limit} {uN} \t "                   \
  "how many child branches ({uN}) in an iteration are allowed to fail due to " \
  "complexity violations before the loop gets blacklisted\n"                   \
  " {y--graphml-witness} {ufilename} \t write the witness in GraphML format "  \
  "to {ufilename}\n"                                                           \
  " {y--symex-cache-dereferences} \t enable caching of repeated "              \
  "dereferences\n"

#endif // CPROVER_GOTO_CHECKER_BMC_UTIL_H

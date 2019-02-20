/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#ifndef CPROVER_GOTO_CHECKER_REPORT_UTIL_H
#define CPROVER_GOTO_CHECKER_REPORT_UTIL_H

#include "properties.h"

struct fault_location_infot;
class goto_trace_storaget;
class goto_tracet;
struct trace_optionst;
class ui_message_handlert;

void report_success(ui_message_handlert &);
void report_failure(ui_message_handlert &);
void report_inconclusive(ui_message_handlert &);
void report_error(ui_message_handlert &);

void output_properties(
  const propertiest &properties,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler);

void output_properties_with_traces(
  const propertiest &properties,
  const goto_trace_storaget &traces,
  const trace_optionst &trace_options,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler);

void output_properties_with_fault_localization(
  const propertiest &properties,
  const std::unordered_map<irep_idt, fault_location_infot> &,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler);

void output_properties_with_traces_and_fault_localization(
  const propertiest &properties,
  const goto_trace_storaget &traces,
  const trace_optionst &trace_options,
  const std::unordered_map<irep_idt, fault_location_infot> &,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler);

void output_error_trace_with_fault_localization(
  const goto_tracet &,
  const namespacet &,
  const trace_optionst &,
  const fault_location_infot &,
  ui_message_handlert &);

void output_overall_result(
  resultt result,
  ui_message_handlert &ui_message_handler);

#endif // CPROVER_GOTO_CHECKER_REPORT_UTIL_H

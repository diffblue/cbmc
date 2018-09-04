/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#ifndef CPROVER_CBMC_BMC_UTIL_H
#define CPROVER_CBMC_BMC_UTIL_H

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

void output_graphml(
  safety_checkert::resultt,
  const goto_tracet &,
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

#endif // CPROVER_CBMC_BMC_UTIL_H

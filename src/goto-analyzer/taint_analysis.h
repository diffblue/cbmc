/*******************************************************************\

Module: Taint Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Taint Analysis

#ifndef CPROVER_GOTO_ANALYZER_TAINT_ANALYSIS_H
#define CPROVER_GOTO_ANALYZER_TAINT_ANALYSIS_H

#include <util/message.h>
#include <util/namespace.h>

#include <goto-programs/goto_model.h>

bool taint_analysis(
  goto_modelt &,
  const std::string &taint_file_name,
  message_handlert &,
  bool show_full,
  const optionalt<std::string> &json_output_file_name = {});

#endif // CPROVER_GOTO_ANALYZER_TAINT_ANALYSIS_H

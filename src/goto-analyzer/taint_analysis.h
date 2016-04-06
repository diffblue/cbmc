/*******************************************************************\

Module: Taint Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TAINT_ANALYSIS_H
#define CPROVER_TAINT_ANALYSIS_H

#include <util/message.h>
#include <util/namespace.h>

#include <goto-programs/goto_functions.h>

bool taint_analysis(
  goto_functionst &,
  const namespacet &,
  const std::string &taint_file_name,
  message_handlert &,
  bool show_full,
  const std::string &json_file_name);

#endif

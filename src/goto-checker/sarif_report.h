/*******************************************************************\

Module: SARIF Report

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// SARIF Report

#ifndef CPROVER_GOTO_CHECKER_SARIF_REPORT_H
#define CPROVER_GOTO_CHECKER_SARIF_REPORT_H

#include "properties.h"

#include <iosfwd>
#include <string>

/// Write a complete SARIF 2.1.0 log to \p out for the given \p properties.
/// \param properties: the verification results
/// \param program: tool name (e.g. "cbmc")
/// \param version: tool version string (e.g. CBMC_VERSION)
/// \param out: output stream
void sarif_report(
  const propertiest &properties,
  const std::string &program,
  const std::string &version,
  std::ostream &out);

#endif // CPROVER_GOTO_CHECKER_SARIF_REPORT_H

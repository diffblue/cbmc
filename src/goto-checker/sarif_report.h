/*******************************************************************\

Module: SARIF Report

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// SARIF Report

#ifndef CPROVER_GOTO_CHECKER_SARIF_REPORT_H
#define CPROVER_GOTO_CHECKER_SARIF_REPORT_H

#include "properties.h"

#include <fstream>
#include <string>

class cmdlinet;
class message_handlert;

#define OPT_SARIF_RESULT "(sarif-result):"

#define HELP_SARIF_RESULT                                                      \
  " {y--sarif-result} {ufile} \t write the verification results to {ufile} "   \
  "in SARIF 2.1.0 format ({y-} for standard output)\n"

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

/// Turn the file name \p file of a source location into a SARIF
/// `artifactLocation.uri` (RFC 3986): an absolute path becomes a `file:` URI,
/// a relative one a relative reference, and characters other than unreserved
/// ones and `/` are percent-encoded. Returns an empty string for names that
/// are not files, such as `<builtin-library-malloc>`.
std::string sarif_uri(const std::string &file);

/// Implements `--sarif-result`: opens the output file before verification,
/// so that a file that cannot be written is reported before any work is
/// done, and writes the results once they are available.
class sarif_outputt
{
public:
  /// \param cmdline: the command line, `--sarif-result` is read from it
  /// \param program: tool name (e.g. "cbmc")
  /// \param message_handler: for diagnostics
  sarif_outputt(
    const cmdlinet &cmdline,
    const std::string &program,
    message_handlert &message_handler);

  /// Warns if `--sarif-result` was given but no results were written,
  /// because the tool did not perform verification (e.g. with
  /// `--show-properties`).
  ~sarif_outputt();

  /// Whether `--sarif-result` was given.
  bool enabled() const
  {
    return !filename.empty();
  }

  /// Whether the SARIF log goes to standard output.
  bool to_stdout() const
  {
    return filename == "-";
  }

  /// Open the output file, if any.
  /// \return false, after reporting an error, if it cannot be opened
  bool open();

  /// Write the SARIF log for \p properties.
  /// \return false, after reporting an error, if writing failed
  bool write(const propertiest &properties);

private:
  std::string filename;
  std::string program;
  message_handlert &message_handler;
  std::ofstream file;
  bool written = false;
};

#endif // CPROVER_GOTO_CHECKER_SARIF_REPORT_H

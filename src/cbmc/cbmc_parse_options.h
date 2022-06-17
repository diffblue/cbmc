/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#ifndef CPROVER_CBMC_CBMC_PARSE_OPTIONS_H
#define CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_trace.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/goto_check_c.h>
#include <goto-checker/bmc_util.h>
#include <goto-instrument/cover.h>
#include <json/json_interface.h>
#include <langapi/language.h>
#include <solvers/strings/string_refinement.h>
#include <xmllang/xml_interface.h>

class optionst;

// clang-format off
#define CBMC_OPTIONS \
  OPT_BMC \
  "(preprocess)(slice-by-trace):" \
  OPT_FUNCTIONS \
  "(no-simplify)(full-slice)" \
  OPT_REACHABILITY_SLICER \
  "(no-propagation)(no-simplify-if)" \
  "(document-subgoals)(test-preprocessor)" \
  "(show-array-constraints)"  \
  OPT_CONFIG_C_CPP \
  OPT_CONFIG_PLATFORM \
  OPT_CONFIG_BACKEND \
  OPT_CONFIG_LIBRARY \
  OPT_GOTO_CHECK \
  OPT_XML_INTERFACE \
  OPT_JSON_INTERFACE \
  OPT_SOLVER \
  OPT_STRING_REFINEMENT_CBMC \
  OPT_SHOW_GOTO_FUNCTIONS \
  "(disable-solver)" \
  "(symex-record-coverage)" \
  "(complexity-graph-roots):" \
  "(show-complexity-graph):" \
  "(show-complexity-graph-with-symex):" \
  "(show-complexity-graph-with-solver):" \
  OPT_SHOW_PROPERTIES \
  "(show-symbol-table)(show-parse-tree)" \
  "(drop-unused-functions)" \
  "(havoc-undefined-functions)" \
  "(property):(stop-on-fail)(trace)" \
  "(verbosity):(no-library)" \
  "(nondet-static)" \
  "(version)" \
  OPT_COVER \
  "(symex-coverage-report):" \
  "(mm):" \
  OPT_TIMESTAMP \
  "(arrays-uf-always)(arrays-uf-never)" \
  OPT_FLUSH \
  "(localize-faults)" \
  OPT_GOTO_TRACE \
  OPT_VALIDATE \
  OPT_ANSI_C_LANGUAGE \
  "(claim):(show-claims)(floatbv)(all-claims)(all-properties)" // legacy, and will eventually disappear // NOLINT(whitespace/line_length)
// clang-format on

class cbmc_parse_optionst : public parse_options_baset
{
public:
  virtual int doit() override;
  virtual void help() override;

  cbmc_parse_optionst(int argc, const char **argv);
  cbmc_parse_optionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

  /// \brief Set the options that have default values
  ///
  /// This function can be called from clients that wish to emulate CBMC's
  /// default behaviour, for example unit tests.
  static void set_default_options(optionst &);

  static bool process_goto_program(goto_modelt &, const optionst &, messaget &);

  static int get_goto_program(
    goto_modelt &,
    const optionst &,
    const cmdlinet &,
    ui_message_handlert &);

protected:
  goto_modelt goto_model;

  void register_languages() override;
  void get_command_line_options(optionst &);
  void preprocessing(const optionst &);
  bool set_properties();
};

#endif // CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

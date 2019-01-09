/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#ifndef CPROVER_CBMC_CBMC_PARSE_OPTIONS_H
#define CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/c_object_factory_parameters.h>

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <langapi/language.h>

#include <analyses/goto_check.h>

#include <goto-checker/bmc_util.h>
#include <goto-checker/solver_factory.h>

#include <goto-programs/goto_trace.h>

#include <solvers/refinement/string_refinement.h>

#include "bmc.h"
#include "xml_interface.h"

class goto_functionst;
class optionst;

// clang-format off
#define CBMC_OPTIONS \
  OPT_BMC \
  "(preprocess)(slice-by-trace):" \
  OPT_FUNCTIONS \
  "(no-simplify)(full-slice)" \
  OPT_REACHABILITY_SLICER \
  "(debug-level):(no-propagation)(no-simplify-if)" \
  "(document-subgoals)(outfile):(test-preprocessor)" \
  "D:I:(c89)(c99)(c11)(cpp98)(cpp03)(cpp11)" \
  "(object-bits):" \
  OPT_GOTO_CHECK \
  "(no-assertions)(no-assumptions)" \
  "(xml-ui)(xml-interface)(json-ui)" \
  "(smt1)(smt2)(fpa)(cvc3)(cvc4)(boolector)(yices)(z3)(mathsat)" \
  "(cprover-smt2)" \
  "(no-sat-preprocessor)" \
  "(beautify)" \
  "(dimacs)(refine)(max-node-refinement):(refine-arrays)(refine-arithmetic)"\
  OPT_STRING_REFINEMENT_CBMC \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  "(show-symbol-table)(show-parse-tree)" \
  "(drop-unused-functions)" \
  "(property):(stop-on-fail)(trace)" \
  "(error-label):(verbosity):(no-library)" \
  "(nondet-static)" \
  "(version)" \
  "(cover):(symex-coverage-report):" \
  "(mm):" \
  OPT_TIMESTAMP \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)(gcc)" \
  "(ppc-macos)(unsigned-char)" \
  "(arrays-uf-always)(arrays-uf-never)" \
  "(string-abstraction)(no-arch)(arch):" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  OPT_FLUSH \
  "(localize-faults)(localize-faults-method):" \
  OPT_GOTO_TRACE \
  OPT_VALIDATE \
  OPT_ANSI_C_LANGUAGE \
  "(claim):(show-claims)(floatbv)(all-claims)(all-properties)" // legacy, and will eventually disappear // NOLINT(whitespace/line_length)
// clang-format on

class cbmc_parse_optionst:
  public parse_options_baset,
  public xml_interfacet,
  public messaget
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
    messaget &,
    ui_message_handlert &);

protected:
  goto_modelt goto_model;
  ui_message_handlert ui_message_handler;
  const path_strategy_choosert path_strategy_chooser;

  void register_languages();
  void get_command_line_options(optionst &);
  void preprocessing(const optionst &);
  bool set_properties();
};

#endif // CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

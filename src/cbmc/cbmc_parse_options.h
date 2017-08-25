/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#ifndef CPROVER_CBMC_CBMC_PARSE_OPTIONS_H
#define CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>

#include <analyses/goto_check.h>

#include <java_bytecode/java_bytecode_language.h>

#include "xml_interface.h"

class bmct;
class goto_functionst;
class optionst;

#define CBMC_OPTIONS \
  "(program-only)(function):(preprocess)(slice-by-trace):" \
  "(no-simplify)(unwind):(unwindset):(slice-formula)(full-slice)" \
  "(debug-level):(no-propagation)(no-simplify-if)" \
  "(document-subgoals)(outfile):(test-preprocessor)" \
  "D:I:(c89)(c99)(c11)(cpp89)(cpp99)(cpp11)" \
  "(object-bits):" \
  "(classpath):(cp):(main-class):" \
  "(depth):(partial-loops)(no-unwinding-assertions)(unwinding-assertions)" \
  OPT_GOTO_CHECK \
  "(no-assertions)(no-assumptions)" \
  "(no-built-in-assertions)" \
  "(xml-ui)(xml-interface)(json-ui)" \
  "(smt1)(smt2)(fpa)(cvc3)(cvc4)(boolector)(yices)(z3)(opensmt)(mathsat)" \
  "(no-sat-preprocessor)" \
  "(no-pretty-names)(beautify)" \
  "(dimacs)(refine)(max-node-refinement):(refine-arrays)(refine-arithmetic)"\
  "(refine-strings)" \
  "(string-non-empty)" \
  "(string-printable)" \
  "(string-max-length):" \
  "(aig)(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  "(show-goto-functions)(show-loops)" \
  "(show-symbol-table)(show-parse-tree)(show-vcc)" \
  "(show-claims)(claim):(show-properties)" \
  "(drop-unused-functions)" \
  "(property):(stop-on-fail)(trace)" \
  "(error-label):(verbosity):(no-library)" \
  "(nondet-static)" \
  "(version)" \
  "(cover):(symex-coverage-report):" \
  "(mm):" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)(gcc)" \
  "(ppc-macos)(unsigned-char)" \
  "(arrays-uf-always)(arrays-uf-never)" \
  "(string-abstraction)(no-arch)(arch):" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  "(graphml-witness):" \
  JAVA_BYTECODE_LANGUAGE_OPTIONS \
  "(java-unwind-enum-static)" \
  "(localize-faults)(localize-faults-method):" \
  "(fixedbv)(floatbv)(all-claims)(all-properties)" // legacy, and will eventually disappear // NOLINT(whitespace/line_length)

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

protected:
  goto_modelt goto_model;
  ui_message_handlert ui_message_handler;

  void eval_verbosity();
  void register_languages();
  void get_command_line_options(optionst &options);
  void preprocessing();
  int get_goto_program(const optionst &);
  bool process_goto_program(const optionst &);
  bool set_properties();
  int do_bmc(bmct &);
};

#endif // CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

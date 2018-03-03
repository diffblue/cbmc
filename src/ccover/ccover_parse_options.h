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

#include <langapi/language.h>

#include <goto-programs/goto_model.h>

#include <cbmc/bmc.h>

#include "ccover_bmc.h"

class optionst;

// clang-format off
#define CCOVER_OPTIONS \
  OPT_BMC \
  "(preprocess)(slice-by-trace):" \
  OPT_FUNCTIONS \
  "(no-simplify)(full-slice)" \
  "(debug-level):(no-propagation)(no-simplify-if)" \
  "(document-subgoals)(outfile):(test-preprocessor)" \
  "D:I:(c89)(c99)(c11)(cpp98)(cpp03)(cpp11)" \
  "(object-bits):" \
  "(no-assumptions)" \
  "(xml-ui)(xml-interface)(json-ui)" \
  "(smt2)(fpa)(cvc4)(boolector)(yices)(z3)(opensmt)(mathsat)" \
  "(no-sat-preprocessor)" \
  "(beautify)" \
  "(dimacs)(refine)(max-node-refinement):(refine-arrays)(refine-arithmetic)"\
  "(refine-strings)" \
  "(string-printable)" \
  "(string-max-length):" \
  "(string-max-input-length):" \
  "(aig)(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  "(show-symbol-table)(show-parse-tree)" \
  "(drop-unused-functions)" \
  "(verbosity):(no-library)" \
  "(nondet-static)" \
  "(version)" \
  "(cover):" \
  "(mm):" \
  OPT_TIMESTAMP \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)(gcc)" \
  "(ppc-macos)(unsigned-char)" \
  "(arrays-uf-always)(arrays-uf-never)" \
  "(string-abstraction)(no-arch)(arch):" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  OPT_GOTO_TRACE \
  "(fixedbv)"
// clang-format on

class ccover_parse_optionst:
  public parse_options_baset,
  public messaget
{
public:
  virtual int doit() override;
  virtual void help() override;

  ccover_parse_optionst(int argc, const char **argv);

protected:
  goto_modelt goto_model;
  ui_message_handlert ui_message_handler;

  void eval_verbosity();
  void register_languages();
  void get_command_line_options(optionst &);
  void preprocessing();
  int get_goto_program(const optionst &);
  bool process_goto_program(const optionst &);
};

#endif // CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

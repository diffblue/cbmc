/*******************************************************************\

Module: JBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JBMC Command Line Option Processing

#ifndef CPROVER_JBMC_JBMC_PARSE_OPTIONS_H
#define CPROVER_JBMC_JBMC_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <langapi/language.h>

#include <goto-checker/bmc_util.h>

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/goto_trace.h>
#include <goto-programs/show_properties.h>

#include <solvers/strings/string_refinement.h>

#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_trace_validation.h>

#include <json/json_interface.h>
#include <xmllang/xml_interface.h>

class goto_functiont;
class goto_model_functiont;
class optionst;

// clang-format off
#define JBMC_OPTIONS \
  OPT_BMC \
  "(preprocess)" \
  OPT_FUNCTIONS \
  "(no-simplify)(full-slice)" \
  OPT_REACHABILITY_SLICER \
  "(debug-level):(no-propagation)(no-simplify-if)" \
  "(document-subgoals)" \
  "(object-bits):" \
  "(classpath):(cp):" \
  OPT_JAVA_JAR \
  "(main-class):" \
  OPT_JAVA_GOTO_BINARY \
  "(no-assertions)(no-assumptions)" \
  OPT_XML_INTERFACE \
  OPT_JSON_INTERFACE \
  "(smt1)" /* rejected, will eventually disappear */ \
  OPT_SOLVER \
  OPT_STRING_REFINEMENT \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_CLASS_HIERARCHY \
  "(show-loops)" \
  "(show-symbol-table)" \
  "(list-symbols)" \
  "(show-parse-tree)" \
  OPT_SHOW_PROPERTIES \
  "(drop-unused-functions)" \
  "(property):(stop-on-fail)(trace)" \
  "(verbosity):" \
  "(nondet-static)" \
  OPT_JAVA_TRACE_VALIDATION \
  "(version)" \
  "(symex-coverage-report):" \
  OPT_TIMESTAMP \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)" \
  "(ppc-macos)" \
  "(arrays-uf-always)(arrays-uf-never)" \
  "(no-arch)(arch):" \
  OPT_FLUSH \
  JAVA_BYTECODE_LANGUAGE_OPTIONS \
  "(java-unwind-enum-static)" \
  "(localize-faults)" \
  "(java-threading)" \
  OPT_GOTO_TRACE \
  OPT_VALIDATE \
  "(symex-driven-lazy-loading)"
// clang-format on

class jbmc_parse_optionst : public parse_options_baset
{
public:
  virtual int doit() override;
  virtual void help() override;

  jbmc_parse_optionst(int argc, const char **argv);
  jbmc_parse_optionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

  /// \brief Set the options that have default values
  ///
  /// This function can be called from clients that wish to emulate JBMC's
  /// default behaviour, for example unit tests.
  static void set_default_options(optionst &);

  void process_goto_function(
    goto_model_functiont &function,
    const abstract_goto_modelt &,
    const optionst &);
  bool process_goto_functions(goto_modelt &goto_model, const optionst &options);

  bool can_generate_function_body(const irep_idt &name);

  bool generate_function_body(
    const irep_idt &function_name,
    symbol_table_baset &symbol_table,
    goto_functiont &function,
    bool body_available);

protected:
  java_object_factory_parameterst object_factory_params;
  bool stub_objects_are_not_null;

  std::unique_ptr<class_hierarchyt> class_hierarchy;

  void get_command_line_options(optionst &);
  int get_goto_program(
    std::unique_ptr<abstract_goto_modelt> &goto_model,
    const optionst &);
  bool show_loaded_functions(const abstract_goto_modelt &goto_model);
  bool show_loaded_symbols(const abstract_goto_modelt &goto_model);

  /// See java_bytecode_languaget::method_context.
  /// The two fields are initialized in exactly the same way.
  /// TODO Refactor this so it only needs to be computed once, in one place.
  optionalt<prefix_filtert> method_context;
};

#endif // CPROVER_JBMC_JBMC_PARSE_OPTIONS_H

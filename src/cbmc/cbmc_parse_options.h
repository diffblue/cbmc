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

#include <util/cmdline_definition.h>
#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <langapi/language.h>

#include <analyses/goto_check.h>

#include <goto-checker/bmc_util.h>
#include <goto-checker/solver_factory.h>

#include <goto-programs/goto_trace.h>

#include <solvers/strings/string_refinement.h>

#include "xml_interface.h"

class goto_functionst;
class optionst;

// clang-format off
const cmdline_definitiont ui_options
{
  {
    "json-ui",
    {},
    "use JSON-formatted output",
    "Other options",
    {}
  },
  {
    "xml-ui",
    {},
    "use XML-formatted output",
    "Other options",
    {}
  }
};

const cmdline_definitiont cbmc_options(
  ui_options
  + cmdline_definitiont{
    {
      "preprocess",
      {},
      "stop after preprocessing. "
      "This is a veeeeeeeeeeeeeeeeery long help text. "
      "This is a veeeeeeeeeeeeeeeeery long help text.",
      "C/C++ frontend options",
      {}
    },
    {
      "slice-by-trace",
      cmdline_optiont::argumentt{"f", "string"},
      "",
      "",
      cmdline_optiont::deprecatedt("-slice-by-trace has been removed")
    }
  }
  + ui_options);
// clang-format on

class cbmc_parse_optionst : public parse_options_baset, public xml_interfacet
{
public:
  virtual int doit() override;
  virtual void help() override;

  cbmc_parse_optionst(int argc, const char **argv);
  cbmc_parse_optionst(
    int argc,
    const char **argv,
    const cmdline_definitiont &extra_options);

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

  void register_languages();
  void get_command_line_options(optionst &);
  void preprocessing(const optionst &);
  bool set_properties();
};

#endif // CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

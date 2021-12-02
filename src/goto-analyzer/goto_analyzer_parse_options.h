/*******************************************************************\

Module: Goto-Analyser Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto-Analyser Command Line Option Processing
///
/// Goto-analyze is the tool front-end for CPROVER's classic style abstract
/// interpretation analyses.  By "classic style" I mean, domains are C++
/// objects, transformers are computed using C++ functions and the
/// fix-points are computed by iteration.  This is in contrast to 2LS's
/// approach where everything is computed using quantifier-elimination.
///
/// The analyses are mostly in analyses/ and although they are used in other
/// places in the code, the goal is that goto-analyze should eventually
/// provide an executable front-end for all of them.
///
/// There are a lot of different analyses and a lot of ways they can be
/// used.  Goto-analyze has six, largely independent, sets of options:
///
/// 1. Task : What you do once you've computed the domains.
/// 2. Abstract interpreter : What kind of abstract interpretation you do.
/// 3. History : What kind of steps and CFG sensitivity the interpreter uses.
/// 4. Domain : What domain you use to represent the values of the variables.
///             This includes domain specific configuration.
/// 5. Storage : How many history steps share domains.
/// 6. Output : What you do with the results.
///
/// Formally speaking, 2, 3, 4 and 5 are somewhat artificial distinction as they
/// are all really parts of the "what abstraction" question.
/// However they correspond to parts of our code architecture, so ...
/// they should stay.
///
/// Ideally, the cross product of options should be supported but ... in
/// practice there will always be ones that are not meaningful.  Those
/// should give errors.  In addition there are some analyses which are
/// currently stand alone as they don't fit directly in to this model.  For
/// example the unwind bounds analysis, which is both the task, the abstract
/// interpreter and the output.  Where possible these should be integrated /
/// support the other options.  In the case of the unwind analysis this
/// means the domain and it's sensitivity should be configurable.
///
///
/// Task
/// ----
///
/// Tasks are implemented by the relevant file in goto-analyze/static_*. At
/// the moment they are each responsible for building the domain / using the
/// other options.  As much as possible of this code should be shared.  Some
/// of these inherit from messaget.  They all probably should.
///
/// Show : Prints out the domains for inspection or further use.
///
/// Verify : Uses the domain to check all assertions in the code, marking
/// each one "SUCCESS" (the assertion always holds), "FAILURE if
/// reachable" (the assertion never holds), "UNKNOWN" (the assertion may or
/// may not hold).  This is implemented using domain_simplify().
///
/// Simplify : Generates a new goto program with branch conditions,
/// assertions, assumptions and assignments simplified using the information
/// in the domain (again using domain_simplify()).  This task is intended to
/// be used as a preprocessing step for other analysis.
///
/// Instrument : (Not implemented yet) Use the domains to add assume()
/// statements to the code giving invariants generated from the domain.
/// These assumes don't reduce the space of possible executions; they make
/// existing invariants explicit.  Again, intended as a preprocessing step.
///
///
/// Abstract Interpreter
/// --------------------
///
/// This option is effectively about how we compute the fix-point(s) /
/// which child class of ai_baset we use.  This and the other AI related
/// option categories (history, domain, storage, etc.) are more extensively
/// documented in analyses/ai.h and analyses/ai_*.h
///
///
/// Output
/// ------
///
/// Text, XML, JSON plus some others for specific domains such as dependence
/// graphs in DOT format.

#ifndef CPROVER_GOTO_ANALYZER_GOTO_ANALYZER_PARSE_OPTIONS_H
#define CPROVER_GOTO_ANALYZER_GOTO_ANALYZER_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <langapi/language.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>

#include <analyses/goto_check_c.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

class optionst;

// clang-format off
#define GOTO_ANALYSER_OPTIONS_TASKS \
  "(show)(verify)(simplify):" \
  "(show-on-source)" \
  "(unreachable-instructions)(unreachable-functions)" \
  "(reachable-functions)"

#define GOTO_ANALYSER_OPTIONS_AI \
  "(recursive-interprocedural)" \
  "(three-way-merge)" \
  "(legacy-ait)" \
  "(legacy-concurrent)"

#define GOTO_ANALYSER_OPTIONS_HISTORY \
  "(ahistorical)" \
  "(call-stack):" \
  "(loop-unwind):" \
  "(branching):" \
  "(loop-unwind-and-branching):"

#define GOTO_ANALYSER_OPTIONS_DOMAIN \
  "(intervals)" \
  "(non-null)" \
  "(constants)" \
  "(dependence-graph)" \
  "(vsd)(variable-sensitivity)" \
  "(dependence-graph-vs)" \

#define GOTO_ANALYSER_OPTIONS_STORAGE \
  "(one-domain-per-history)" \
  "(one-domain-per-location)"

#define GOTO_ANALYSER_OPTIONS_OUTPUT \
  "(json):(xml):" \
  "(text):(dot):"

#define GOTO_ANALYSER_OPTIONS_SPECIFIC_ANALYSES \
  "(taint):(show-taint)" \
  "(show-local-may-alias)"

#define GOTO_ANALYSER_OPTIONS \
  OPT_FUNCTIONS \
  OPT_CONFIG_C_CPP \
  OPT_CONFIG_PLATFORM \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  OPT_GOTO_CHECK \
  "(show-loops)" \
  "(show-symbol-table)(show-parse-tree)" \
  "(show-reachable-properties)(property):" \
  "(verbosity):(version)" \
  OPT_FLUSH \
  OPT_TIMESTAMP \
  OPT_VALIDATE \
  GOTO_ANALYSER_OPTIONS_TASKS \
  "(no-simplify-slicing)" \
  "(show-intervals)(show-non-null)" \
  GOTO_ANALYSER_OPTIONS_AI \
  "(location-sensitive)(concurrent)" \
  GOTO_ANALYSER_OPTIONS_HISTORY \
  GOTO_ANALYSER_OPTIONS_DOMAIN \
  OPT_VSD \
  GOTO_ANALYSER_OPTIONS_STORAGE  \
  GOTO_ANALYSER_OPTIONS_OUTPUT \
  GOTO_ANALYSER_OPTIONS_SPECIFIC_ANALYSES \
// clang-format on

class goto_analyzer_parse_optionst: public parse_options_baset
{
public:
  virtual int doit() override;
  virtual void help() override;

  goto_analyzer_parse_optionst(int argc, const char **argv);

protected:
  goto_modelt goto_model;

  void register_languages() override;

  virtual void get_command_line_options(optionst &options);

  virtual bool process_goto_program(const optionst &options);

  virtual int perform_analysis(const optionst &options);
};

#endif // CPROVER_GOTO_ANALYZER_GOTO_ANALYZER_PARSE_OPTIONS_H

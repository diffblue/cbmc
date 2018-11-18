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
/// used.  Goto-analyze has five, largely independent, sets of options:
///
/// 1. Task : What you do once you've computed the domains.
/// 2. Abstract interpreter : What kind of abstract interpretation you do.
/// 3. Domain : What domain you use.
/// 4. Sensitivity : How that domain handles things like arrays, pointers, etc.
///    (see variable_sensitivity_domain.h)
/// 5. Output : What you do with the results.
///
/// Formally speaking, 2, 3 and 4 are an artificial distinction as they are
/// all really parts of the "what domain" question.  However they correspond
/// to parts of our code architecture, so ... they should stay.
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
/// which child class of ai_baset we use.  I.E.  ait<domainT> or
/// concurrency_aware_ait<domainT>, etc.   For migrating / refactor /
/// unifying with the pointer analysis code we might want a
/// location_insensitive_ait<domainT> or something but this is not urgent.
/// We will need a context_aware_ait<domainT>.
///
///
/// Domain
/// ------
///
/// Which child of ai_domain_baset we use to represent the abstract state at
/// each location / implement the transformers.  I expect most of these will
/// be non-relational (i.e. an abstract object for each variable) due to the
/// cost of implementing effective non-relational domains in this style vs.
/// using 2LS.  The exception might be equalities, which we could implement
/// here.
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

#include <analyses/ai.h>
#include <analyses/goto_check.h>

class bmct;
class goto_functionst;
class optionst;

// clang-format off
#define GOTO_ANALYSER_OPTIONS \
  OPT_FUNCTIONS \
  "D:I:(std89)(std99)(std11)" \
  "(classpath):(cp):(main-class):" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  OPT_GOTO_CHECK \
  "(show-loops)" \
  "(show-symbol-table)(show-parse-tree)" \
  "(show-reachable-properties)(property):" \
  "(verbosity):(version)" \
  "(gcc)(arch):" \
  "(taint):(show-taint)" \
  "(show-local-may-alias)" \
  "(json):(xml):" \
  "(text):(dot):" \
  OPT_FLUSH \
  OPT_TIMESTAMP \
  "(unreachable-instructions)(unreachable-functions)" \
  "(reachable-functions)" \
  "(intervals)(show-intervals)" \
  "(non-null)(show-non-null)" \
  "(constants)" \
  "(dependence-graph)" \
  "(show)(verify)(simplify):" \
  "(show-on-source)" \
  "(location-sensitive)(concurrent)" \
  "(no-simplify-slicing)" \
  OPT_VALIDATE \
// clang-format on

class goto_analyzer_parse_optionst:
  public parse_options_baset,
  public messaget
{
public:
  virtual int doit() override;
  virtual void help() override;

  goto_analyzer_parse_optionst(int argc, const char **argv);

protected:
  ui_message_handlert ui_message_handler;
  goto_modelt goto_model;

  virtual void register_languages();

  virtual void get_command_line_options(optionst &options);

  virtual bool process_goto_program(const optionst &options);
  bool set_properties();

  virtual int perform_analysis(const optionst &options);

  ai_baset *build_analyzer(const optionst &, const namespacet &ns);

  ui_message_handlert::uit get_ui()
  {
    return ui_message_handler.get_ui();
  }
};

#endif // CPROVER_GOTO_ANALYZER_GOTO_ANALYZER_PARSE_OPTIONS_H

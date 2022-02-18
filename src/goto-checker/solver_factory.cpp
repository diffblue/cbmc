/*******************************************************************\

Module: Solver Factory

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Solver Factory

#include "solver_factory.h"

#include <util/cmdline.h>
#include <util/exception_utils.h>
#include <util/make_unique.h>
#include <util/message.h>
#include <util/options.h>
#include <util/version.h>

#include <iostream>

#ifdef _MSC_VER
#include <util/unicode.h>
#endif

#include <solvers/stack_decision_procedure.h>

#include <solvers/flattening/bv_dimacs.h>
#include <solvers/prop/prop.h>
#include <solvers/prop/solver_resource_limits.h>
#include <solvers/refinement/bv_refinement.h>
#include <solvers/sat/dimacs_cnf.h>
#include <solvers/sat/external_sat.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt2_incremental/smt2_incremental_decision_procedure.h>
#include <solvers/smt2_incremental/smt_solver_process.h>
#include <solvers/strings/string_refinement.h>

#include <goto-symex/solver_hardness.h>

solver_factoryt::solver_factoryt(
  const optionst &_options,
  const namespacet &_ns,
  message_handlert &_message_handler,
  bool _output_xml_in_refinement)
  : options(_options),
    ns(_ns),
    message_handler(_message_handler),
    output_xml_in_refinement(_output_xml_in_refinement)
{
}

solver_factoryt::solvert::solvert(std::unique_ptr<decision_proceduret> p)
  : decision_procedure_ptr(std::move(p))
{
}

solver_factoryt::solvert::solvert(
  std::unique_ptr<decision_proceduret> p1,
  std::unique_ptr<propt> p2)
  : prop_ptr(std::move(p2)), decision_procedure_ptr(std::move(p1))
{
}

solver_factoryt::solvert::solvert(
  std::unique_ptr<decision_proceduret> p1,
  std::unique_ptr<std::ofstream> p2)
  : ofstream_ptr(std::move(p2)), decision_procedure_ptr(std::move(p1))
{
}

decision_proceduret &solver_factoryt::solvert::decision_procedure() const
{
  PRECONDITION(decision_procedure_ptr != nullptr);
  return *decision_procedure_ptr;
}

stack_decision_proceduret &
solver_factoryt::solvert::stack_decision_procedure() const
{
  PRECONDITION(decision_procedure_ptr != nullptr);
  stack_decision_proceduret *solver =
    dynamic_cast<stack_decision_proceduret *>(&*decision_procedure_ptr);
  INVARIANT(solver != nullptr, "stack decision procedure required");
  return *solver;
}

propt &solver_factoryt::solvert::prop() const
{
  PRECONDITION(prop_ptr != nullptr);
  return *prop_ptr;
}

void solver_factoryt::set_decision_procedure_time_limit(
  decision_proceduret &decision_procedure)
{
  const int timeout_seconds =
    options.get_signed_int_option("solver-time-limit");

  if(timeout_seconds > 0)
  {
    solver_resource_limitst *solver =
      dynamic_cast<solver_resource_limitst *>(&decision_procedure);
    if(solver == nullptr)
    {
      messaget log(message_handler);
      log.warning() << "cannot set solver time limit on "
                    << decision_procedure.decision_procedure_text()
                    << messaget::eom;
      return;
    }

    solver->set_time_limit_seconds(timeout_seconds);
  }
}

void solver_factoryt::solvert::set_decision_procedure(
  std::unique_ptr<decision_proceduret> p)
{
  decision_procedure_ptr = std::move(p);
}

void solver_factoryt::solvert::set_prop(std::unique_ptr<propt> p)
{
  prop_ptr = std::move(p);
}

void solver_factoryt::solvert::set_ofstream(std::unique_ptr<std::ofstream> p)
{
  ofstream_ptr = std::move(p);
}

std::unique_ptr<solver_factoryt::solvert> solver_factoryt::get_solver()
{
  if(options.get_bool_option("dimacs"))
    return get_dimacs();
  if(options.is_set("external-sat-solver"))
    return get_external_sat();
  if(
    options.get_bool_option("refine") &&
    !options.get_bool_option("refine-strings"))
  {
    return get_bv_refinement();
  }
  else if(options.get_bool_option("refine-strings"))
    return get_string_refinement();
  const auto incremental_smt2_solver =
    options.get_option("incremental-smt2-solver");
  if(!incremental_smt2_solver.empty())
    return get_incremental_smt2(incremental_smt2_solver);
  if(options.get_bool_option("smt2"))
    return get_smt2(get_smt2_solver_type());
  return get_default();
}

/// Uses the options to pick an SMT 2.0 solver
/// \return An smt2_dect::solvert giving the solver to use.
smt2_dect::solvert solver_factoryt::get_smt2_solver_type() const
{
  // we shouldn't get here if this option isn't set
  PRECONDITION(options.get_bool_option("smt2"));

  smt2_dect::solvert s = smt2_dect::solvert::GENERIC;

  if(options.get_bool_option("boolector"))
    s = smt2_dect::solvert::BOOLECTOR;
  else if(options.get_bool_option("cprover-smt2"))
    s = smt2_dect::solvert::CPROVER_SMT2;
  else if(options.get_bool_option("mathsat"))
    s = smt2_dect::solvert::MATHSAT;
  else if(options.get_bool_option("cvc3"))
    s = smt2_dect::solvert::CVC3;
  else if(options.get_bool_option("cvc4"))
    s = smt2_dect::solvert::CVC4;
  else if(options.get_bool_option("yices"))
    s = smt2_dect::solvert::YICES;
  else if(options.get_bool_option("z3"))
    s = smt2_dect::solvert::Z3;
  else if(options.get_bool_option("generic"))
    s = smt2_dect::solvert::GENERIC;

  return s;
}

template <typename SatcheckT>
static std::unique_ptr<SatcheckT>
make_satcheck_prop(message_handlert &message_handler, const optionst &options)
{
  auto satcheck = util_make_unique<SatcheckT>(message_handler);
  if(options.is_set("write-solver-stats-to"))
  {
    if(
      auto hardness_collector = dynamic_cast<hardness_collectort *>(&*satcheck))
    {
      std::unique_ptr<solver_hardnesst> solver_hardness =
        util_make_unique<solver_hardnesst>();
      solver_hardness->set_outfile(options.get_option("write-solver-stats-to"));
      hardness_collector->solver_hardness = std::move(solver_hardness);
    }
    else
    {
      messaget log(message_handler);
      log.warning()
        << "Configured solver does not support --write-solver-stats-to. "
        << "Solver stats will not be written." << messaget::eom;
    }
  }
  return satcheck;
}

std::unique_ptr<solver_factoryt::solvert> solver_factoryt::get_default()
{
  auto solver = util_make_unique<solvert>();
  if(
    options.get_bool_option("beautify") ||
    !options.get_bool_option("sat-preprocessor")) // no simplifier
  {
    // simplifier won't work with beautification
    solver->set_prop(
      make_satcheck_prop<satcheck_no_simplifiert>(message_handler, options));
  }
  else // with simplifier
  {
    solver->set_prop(make_satcheck_prop<satcheckt>(message_handler, options));
  }

  bool get_array_constraints =
    options.get_bool_option("show-array-constraints");
  auto bv_pointers = util_make_unique<bv_pointerst>(
    ns, solver->prop(), message_handler, get_array_constraints);

  if(options.get_option("arrays-uf") == "never")
    bv_pointers->unbounded_array = bv_pointerst::unbounded_arrayt::U_NONE;
  else if(options.get_option("arrays-uf") == "always")
    bv_pointers->unbounded_array = bv_pointerst::unbounded_arrayt::U_ALL;

  set_decision_procedure_time_limit(*bv_pointers);
  solver->set_decision_procedure(std::move(bv_pointers));

  return solver;
}

std::unique_ptr<solver_factoryt::solvert> solver_factoryt::get_dimacs()
{
  no_beautification();
  no_incremental_check();

  auto prop = util_make_unique<dimacs_cnft>(message_handler);

  std::string filename = options.get_option("outfile");

  auto bv_dimacs =
    util_make_unique<bv_dimacst>(ns, *prop, message_handler, filename);

  return util_make_unique<solvert>(std::move(bv_dimacs), std::move(prop));
}

std::unique_ptr<solver_factoryt::solvert> solver_factoryt::get_external_sat()
{
  no_beautification();
  no_incremental_check();

  std::string external_sat_solver = options.get_option("external-sat-solver");
  auto prop =
    util_make_unique<external_satt>(message_handler, external_sat_solver);

  auto bv_pointers = util_make_unique<bv_pointerst>(ns, *prop, message_handler);

  return util_make_unique<solvert>(std::move(bv_pointers), std::move(prop));
}

std::unique_ptr<solver_factoryt::solvert> solver_factoryt::get_bv_refinement()
{
  std::unique_ptr<propt> prop = [this]() -> std::unique_ptr<propt> {
    // We offer the option to disable the SAT preprocessor
    if(options.get_bool_option("sat-preprocessor"))
    {
      no_beautification();
      return make_satcheck_prop<satcheckt>(message_handler, options);
    }
    return make_satcheck_prop<satcheck_no_simplifiert>(
      message_handler, options);
  }();

  bv_refinementt::infot info;
  info.ns = &ns;
  info.prop = prop.get();
  info.output_xml = output_xml_in_refinement;

  // we allow setting some parameters
  if(options.get_bool_option("max-node-refinement"))
    info.max_node_refinement =
      options.get_unsigned_int_option("max-node-refinement");

  info.refine_arrays = options.get_bool_option("refine-arrays");
  info.refine_arithmetic = options.get_bool_option("refine-arithmetic");
  info.message_handler = &message_handler;

  auto decision_procedure = util_make_unique<bv_refinementt>(info);
  set_decision_procedure_time_limit(*decision_procedure);
  return util_make_unique<solvert>(
    std::move(decision_procedure), std::move(prop));
}

/// the string refinement adds to the bit vector refinement specifications for
/// functions from the Java string library
/// \return a solver for cbmc
std::unique_ptr<solver_factoryt::solvert>
solver_factoryt::get_string_refinement()
{
  string_refinementt::infot info;
  info.ns = &ns;
  auto prop =
    make_satcheck_prop<satcheck_no_simplifiert>(message_handler, options);
  info.prop = prop.get();
  info.refinement_bound = DEFAULT_MAX_NB_REFINEMENT;
  info.output_xml = output_xml_in_refinement;
  if(options.get_bool_option("max-node-refinement"))
    info.max_node_refinement =
      options.get_unsigned_int_option("max-node-refinement");
  info.refine_arrays = options.get_bool_option("refine-arrays");
  info.refine_arithmetic = options.get_bool_option("refine-arithmetic");
  info.message_handler = &message_handler;

  auto decision_procedure = util_make_unique<string_refinementt>(info);
  set_decision_procedure_time_limit(*decision_procedure);
  return util_make_unique<solvert>(
    std::move(decision_procedure), std::move(prop));
}

std::unique_ptr<solver_factoryt::solvert>
solver_factoryt::get_incremental_smt2(std::string solver_command)
{
  no_beautification();
  auto solver_process = util_make_unique<smt_piped_solver_processt>(
    std::move(solver_command), message_handler);

  return util_make_unique<solvert>(
    util_make_unique<smt2_incremental_decision_proceduret>(
      ns, std::move(solver_process), message_handler));
}

std::unique_ptr<solver_factoryt::solvert>
solver_factoryt::get_smt2(smt2_dect::solvert solver)
{
  no_beautification();

  const std::string &filename = options.get_option("outfile");

  if(filename.empty())
  {
    if(solver == smt2_dect::solvert::GENERIC)
    {
      throw invalid_command_line_argument_exceptiont(
        "required filename not provided",
        "--outfile",
        "provide a filename with --outfile");
    }

    auto smt2_dec = util_make_unique<smt2_dect>(
      ns,
      "cbmc",
      std::string("Generated by CBMC ") + CBMC_VERSION,
      "QF_AUFBV",
      solver,
      message_handler);

    if(options.get_bool_option("fpa"))
      smt2_dec->use_FPA_theory = true;

    set_decision_procedure_time_limit(*smt2_dec);
    return util_make_unique<solvert>(std::move(smt2_dec));
  }
  else if(filename == "-")
  {
    auto smt2_conv = util_make_unique<smt2_convt>(
      ns,
      "cbmc",
      std::string("Generated by CBMC ") + CBMC_VERSION,
      "QF_AUFBV",
      solver,
      std::cout);

    if(options.get_bool_option("fpa"))
      smt2_conv->use_FPA_theory = true;

    set_decision_procedure_time_limit(*smt2_conv);
    return util_make_unique<solvert>(std::move(smt2_conv));
  }
  else
  {
#ifdef _MSC_VER
    auto out = util_make_unique<std::ofstream>(widen(filename));
#else
    auto out = util_make_unique<std::ofstream>(filename);
#endif

    if(!*out)
    {
      throw invalid_command_line_argument_exceptiont(
        "failed to open file: " + filename, "--outfile");
    }

    auto smt2_conv = util_make_unique<smt2_convt>(
      ns,
      "cbmc",
      std::string("Generated by CBMC ") + CBMC_VERSION,
      "QF_AUFBV",
      solver,
      *out);

    if(options.get_bool_option("fpa"))
      smt2_conv->use_FPA_theory = true;

    set_decision_procedure_time_limit(*smt2_conv);
    return util_make_unique<solvert>(std::move(smt2_conv), std::move(out));
  }
}

void solver_factoryt::no_beautification()
{
  if(options.get_bool_option("beautify"))
  {
    throw invalid_command_line_argument_exceptiont(
      "the chosen solver does not support beautification", "--beautify");
  }
}

void solver_factoryt::no_incremental_check()
{
  const bool all_properties = options.get_bool_option("all-properties");
  const bool cover = options.is_set("cover");
  const bool incremental_loop = options.is_set("incremental-loop");

  if(all_properties)
  {
    throw invalid_command_line_argument_exceptiont(
      "the chosen solver does not support incremental solving",
      "--all_properties");
  }
  else if(cover)
  {
    throw invalid_command_line_argument_exceptiont(
      "the chosen solver does not support incremental solving", "--cover");
  }
  else if(incremental_loop)
  {
    throw invalid_command_line_argument_exceptiont(
      "the chosen solver does not support incremental solving",
      "--incremental-loop");
  }
}

static void parse_sat_options(const cmdlinet &cmdline, optionst &options)
{
  if(cmdline.isset("external-sat-solver"))
  {
    options.set_option(
      "external-sat-solver", cmdline.get_value("external-sat-solver"));
  }

  options.set_option("sat-preprocessor", !cmdline.isset("no-sat-preprocessor"));

  if(cmdline.isset("dimacs"))
    options.set_option("dimacs", true);
}

static void parse_smt2_options(const cmdlinet &cmdline, optionst &options)
{
  if(cmdline.isset("smt2"))
    options.set_option("smt2", true);

  if(cmdline.isset("fpa"))
    options.set_option("fpa", true);

  bool solver_set = false;

  if(cmdline.isset("boolector"))
  {
    options.set_option("boolector", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("cprover-smt2"))
  {
    options.set_option("cprover-smt2", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("mathsat"))
  {
    options.set_option("mathsat", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("cvc4"))
  {
    options.set_option("cvc4", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("incremental-smt2-solver"))
  {
    options.set_option(
      "incremental-smt2-solver", cmdline.get_value("incremental-smt2-solver")),
      solver_set = true;
  }

  if(cmdline.isset("yices"))
  {
    options.set_option("yices", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("z3"))
  {
    options.set_option("z3", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("smt2") && !solver_set)
  {
    if(cmdline.isset("outfile"))
    {
      // outfile and no solver should give standard compliant SMT-LIB
      options.set_option("generic", true);
    }
    else
    {
      // the default smt2 solver
      options.set_option("z3", true);
    }
  }
}

void parse_solver_options(const cmdlinet &cmdline, optionst &options)
{
  parse_sat_options(cmdline, options);
  parse_smt2_options(cmdline, options);

  if(cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.get_value("outfile"));

  if(cmdline.isset("write-solver-stats-to"))
  {
    options.set_option(
      "write-solver-stats-to", cmdline.get_value("write-solver-stats-to"));
  }

  if(cmdline.isset("beautify"))
    options.set_option("beautify", true);

  if(cmdline.isset("refine-arrays"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
  }

  if(cmdline.isset("refine-arithmetic"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arithmetic", true);
  }

  if(cmdline.isset("refine"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
    options.set_option("refine-arithmetic", true);
  }

  if(cmdline.isset("max-node-refinement"))
  {
    options.set_option(
      "max-node-refinement", cmdline.get_value("max-node-refinement"));
  }
}

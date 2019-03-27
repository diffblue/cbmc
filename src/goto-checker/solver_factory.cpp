/*******************************************************************\

Module: Solver Factory

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Solver Factory

#include "solver_factory.h"

#include <iostream>

#include <util/exception_utils.h>
#include <util/make_unique.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>
#include <util/version.h>

#ifdef _MSC_VER
#include <util/unicode.h>
#endif

#include <solvers/flattening/bv_dimacs.h>
#include <solvers/prop/decision_procedure_incremental.h>
#include <solvers/prop/prop.h>
#include <solvers/prop/solver_resource_limits.h>
#include <solvers/refinement/bv_refinement.h>
#include <solvers/sat/dimacs_cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/strings/string_refinement.h>

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

decision_procedure_incrementalt &
solver_factoryt::solvert::decision_procedure_incremental() const
{
  PRECONDITION(decision_procedure_ptr != nullptr);
  decision_procedure_incrementalt *solver =
    dynamic_cast<decision_procedure_incrementalt *>(&*decision_procedure_ptr);
  INVARIANT(solver != nullptr, "incremental decision procedure required");
  return *solver;
}

decision_procedure_assumptionst &
solver_factoryt::solvert::decision_procedure_assumptions() const
{
  PRECONDITION(decision_procedure_ptr != nullptr);
  decision_procedure_assumptionst *solver =
    dynamic_cast<decision_procedure_assumptionst *>(&*decision_procedure_ptr);
  INVARIANT(
    solver != nullptr,
    "incremental decision procedure with solving under assumptions required");
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
  if(options.get_bool_option("refine"))
    return get_bv_refinement();
  else if(options.get_bool_option("refine-strings"))
    return get_string_refinement();
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

std::unique_ptr<solver_factoryt::solvert> solver_factoryt::get_default()
{
  auto solver = util_make_unique<solvert>();

  if(
    options.get_bool_option("beautify") ||
    !options.get_bool_option("sat-preprocessor")) // no simplifier
  {
    // simplifier won't work with beautification
    solver->set_prop(
      util_make_unique<satcheck_no_simplifiert>(message_handler));
  }
  else // with simplifier
  {
    solver->set_prop(util_make_unique<satcheckt>(message_handler));
  }

  auto bv_pointers =
    util_make_unique<bv_pointerst>(ns, solver->prop(), message_handler);

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

std::unique_ptr<solver_factoryt::solvert> solver_factoryt::get_bv_refinement()
{
  std::unique_ptr<propt> prop = [this]() -> std::unique_ptr<propt> {
    // We offer the option to disable the SAT preprocessor
    if(options.get_bool_option("sat-preprocessor"))
    {
      no_beautification();
      return util_make_unique<satcheckt>(message_handler);
    }
    return util_make_unique<satcheck_no_simplifiert>(message_handler);
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
  auto prop = util_make_unique<satcheck_no_simplifiert>(message_handler);
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
solver_factoryt::get_smt2(smt2_dect::solvert solver)
{
  no_beautification();

  const std::string &filename = options.get_option("outfile");

  if(filename == "")
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
      solver);
    smt2_dec->set_message_handler(message_handler);

    if(options.get_bool_option("fpa"))
      smt2_dec->use_FPA_theory = true;

    smt2_dec->set_message_handler(message_handler);

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
  const bool incremental_check = options.is_set("incremental-check");

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
  else if(incremental_check)
  {
    throw invalid_command_line_argument_exceptiont(
      "the chosen solver does not support incremental solving",
      "--incremental-check");
  }
}

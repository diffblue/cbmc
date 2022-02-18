/*******************************************************************\

Module: Solver Factory

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Solver Factory

#ifndef CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H
#define CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

#include <memory>

#include <solvers/smt2/smt2_dec.h>

class cmdlinet;
class message_handlert;
class namespacet;
class optionst;
class propt;
class decision_proceduret;
class stack_decision_proceduret;

class solver_factoryt final
{
public:
  /// Note: The solver returned will hold a reference to the namespace `ns`.
  solver_factoryt(
    const optionst &_options,
    const namespacet &_ns,
    message_handlert &_message_handler,
    bool _output_xml_in_refinement);

  // The solver class,
  // which owns a variety of allocated objects.
  class solvert final
  {
  public:
    solvert() = default;
    explicit solvert(std::unique_ptr<decision_proceduret> p);
    solvert(std::unique_ptr<decision_proceduret> p1, std::unique_ptr<propt> p2);
    solvert(
      std::unique_ptr<decision_proceduret> p1,
      std::unique_ptr<std::ofstream> p2);

    decision_proceduret &decision_procedure() const;
    stack_decision_proceduret &stack_decision_procedure() const;
    propt &prop() const;

    void set_decision_procedure(std::unique_ptr<decision_proceduret> p);
    void set_prop(std::unique_ptr<propt> p);
    void set_ofstream(std::unique_ptr<std::ofstream> p);

    // the objects are deleted in the opposite order they appear below
    std::unique_ptr<std::ofstream> ofstream_ptr;
    std::unique_ptr<propt> prop_ptr;
    std::unique_ptr<decision_proceduret> decision_procedure_ptr;
  };

  /// Returns a solvert object
  virtual std::unique_ptr<solvert> get_solver();

  virtual ~solver_factoryt() = default;

protected:
  const optionst &options;
  const namespacet &ns;
  message_handlert &message_handler;
  const bool output_xml_in_refinement;

  std::unique_ptr<solvert> get_default();
  std::unique_ptr<solvert> get_dimacs();
  std::unique_ptr<solvert> get_external_sat();
  std::unique_ptr<solvert> get_bv_refinement();
  std::unique_ptr<solvert> get_string_refinement();
  std::unique_ptr<solvert> get_incremental_smt2(std::string solver_command);
  std::unique_ptr<solvert> get_smt2(smt2_dect::solvert solver);

  smt2_dect::solvert get_smt2_solver_type() const;

  /// Sets the timeout of \p decision_procedure if the `solver-time-limit`
  /// option has a positive value (in seconds).
  /// \note Most solvers silently ignore the time limit at the moment.
  void
  set_decision_procedure_time_limit(decision_proceduret &decision_procedure);

  // consistency checks during solver creation
  void no_beautification();
  void no_incremental_check();
};

/// Parse solver-related command-line parameters in \p cmdline and set
/// corresponding values in \p options.
void parse_solver_options(const cmdlinet &cmdline, optionst &options);

#define OPT_SOLVER                                                             \
  "(smt1)" /* rejected, will eventually disappear */                           \
  "(smt2)"                                                                     \
  "(fpa)" /* undocumented */                                                   \
  "(cvc3)"                                                                     \
  "(cvc4)(boolector)(yices)(z3)"                                               \
  "(mathsat)"                                                                  \
  "(cprover-smt2)"                                                             \
  "(incremental-smt2-solver):"                                                 \
  "(external-sat-solver):"                                                     \
  "(no-sat-preprocessor)" /* undocumented */                                   \
  "(beautify)"                                                                 \
  "(dimacs)"                                                                   \
  "(refine)"                                                                   \
  "(max-node-refinement):" /* undocumented */                                  \
  "(refine-arrays)"        /* undocumented */                                  \
  "(refine-arithmetic)"    /* undocumented */                                  \
  "(outfile):"                                                                 \
  "(write-solver-stats-to):"

#define HELP_SOLVER                                                            \
  " --external-sat-solver cmd    command to invoke SAT solver process\n"       \
  " --dimacs                     generate CNF in DIMACS format\n"              \
  " --beautify                   beautify the counterexample\n"                \
  "                              (greedy heuristic)\n"                         \
  " --smt1                       use default SMT1 solver (obsolete)\n"         \
  " --smt2                       use default SMT2 solver (Z3)\n"               \
  " --boolector                  use Boolector\n"                              \
  " --cprover-smt2               use CPROVER SMT2 solver\n"                    \
  " --cvc3                       use CVC3\n"                                   \
  " --cvc4                       use CVC4\n"                                   \
  " --mathsat                    use MathSAT\n"                                \
  " --yices                      use Yices\n"                                  \
  " --z3                         use Z3\n"                                     \
  " --refine                     use refinement procedure (experimental)\n"    \
  " --incremental-smt2-solver cmd\n"                                           \
  "                              command to invoke external SMT solver for\n"  \
  "                              incremental solving (experimental)\n"         \
  " --outfile filename           output formula to given file\n"               \
  " --write-solver-stats-to json-file\n"                                       \
  "                              collect the solver query complexity\n"

#endif // CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

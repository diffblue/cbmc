/*******************************************************************\

Module: Solver Factory

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Solver Factory

#ifndef CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H
#define CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

#include <solvers/prop/prop.h>
#include <solvers/smt2/smt2_dec.h>

#include <memory>

class cmdlinet;
class message_handlert;
class namespacet;
class optionst;
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
    explicit solvert(std::unique_ptr<decision_proceduret> p);
    solvert(std::unique_ptr<decision_proceduret> p1, std::unique_ptr<propt> p2);
    solvert(
      std::unique_ptr<decision_proceduret> p1,
      std::unique_ptr<std::ofstream> p2);

    decision_proceduret &decision_procedure() const;
    stack_decision_proceduret &stack_decision_procedure() const;

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
  "(fpa)"                                                                      \
  "(cvc3)"                                                                     \
  "(cvc4)(cvc5)(bitwuzla)(boolector)(yices)(z3)"                               \
  "(mathsat)"                                                                  \
  "(cprover-smt2)"                                                             \
  "(incremental-smt2-solver):"                                                 \
  "(sat-solver):"                                                              \
  "(external-sat-solver):"                                                     \
  "(no-sat-preprocessor)"                                                      \
  "(beautify)"                                                                 \
  "(dimacs)"                                                                   \
  "(refine)"                                                                   \
  "(max-node-refinement):"                                                     \
  "(refine-arrays)"                                                            \
  "(refine-arithmetic)"                                                        \
  "(outfile):"                                                                 \
  "(dump-smt-formula):"                                                        \
  "(write-solver-stats-to):"

#define HELP_SOLVER                                                            \
  help_entry("--sat-solver solver", "use specified SAT solver")                \
    << help_entry(                                                             \
         "--external-sat-solver cmd", "command to invoke SAT solver process")  \
    << help_entry(                                                             \
         "--no-sat-preprocessor", "disable the SAT solver's simplifier")       \
    << help_entry("--dimacs", "generate CNF in DIMACS format")                 \
    << help_entry(                                                             \
         "--beautify", "beautify the counterexample (greedy heuristic)")       \
    << help_entry("--smt1", "use default SMT1 solver (obsolete)")              \
    << help_entry("--smt2", "use default SMT2 solver (Z3)")                    \
    << help_entry("--bitwuzla", "use Bitwuzla")                                \
    << help_entry("--boolector", "use Boolector")                              \
    << help_entry("--cprover-smt2", "use CPROVER SMT2 solver")                 \
    << help_entry("--cvc3", "use CVC3") << help_entry("--cvc4", "use CVC4")    \
    << help_entry("--mathsat", "use MathSAT")                                  \
    << help_entry("--yices", "use Yices") << help_entry("--z3", "use Z3")      \
    << help_entry("--fpa", "use theory of floating-point arithmetic")          \
    << help_entry("--refine", "use refinement procedure (experimental)")       \
    << help_entry("--refine-arrays", "use refinement for arrays only")         \
    << help_entry(                                                             \
         "--refine-arithmetic", "refinement of arithmetic expressions only")   \
    << help_entry(                                                             \
         "--max-node-refinement",                                              \
         "maximum refinement iterations for arithmetic expressions")           \
    << help_entry(                                                             \
         "--incremental-smt2-solver cmd",                                      \
         "command to invoke external SMT solver for incremental solving "      \
         "(experimental)")                                                     \
    << help_entry("--outfile filename", "output formula to given file")        \
    << help_entry(                                                             \
         "--dump-smt-formula filename",                                        \
         "output smt incremental formula to the given file")                   \
    << help_entry(                                                             \
         "--write-solver-stats-to json-file",                                  \
         "collect the solver query complexity")

#endif // CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

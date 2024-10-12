/*******************************************************************\

Module: Solver Factory

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Solver Factory

#ifndef CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H
#define CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

#include <goto-symex/solver_hardness.h> // IWYU pragma: keep
#include <solvers/flattening/boolbv.h>
#include <solvers/smt2/smt2_dec.h>

#include <memory>

class cmdlinet;
class message_handlert;
class namespacet;
class optionst;
class solver_resource_limitst;

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
    explicit solvert(std::unique_ptr<stack_decision_proceduret> p);
    solvert(
      std::unique_ptr<stack_decision_proceduret> p1,
      std::unique_ptr<propt> p2);
    solvert(
      std::unique_ptr<stack_decision_proceduret> p1,
      std::unique_ptr<std::ofstream> p2);
    solvert(std::unique_ptr<boolbvt> p1, std::unique_ptr<propt> p2);
    solvert(
      std::unique_ptr<boolbvt> p1,
      std::unique_ptr<propt> p2,
      std::shared_ptr<solver_hardnesst> p3);

    stack_decision_proceduret &decision_procedure() const;
    boolbvt &boolbv_decision_procedure() const;
    solver_hardnesst *hardness_collector() const;

  private:
    std::shared_ptr<solver_hardnesst> hardness_ptr;
    // the objects are deleted in the opposite order they appear below
    std::unique_ptr<std::ofstream> ofstream_ptr;
    std::unique_ptr<propt> prop_ptr;
    std::unique_ptr<stack_decision_proceduret> decision_procedure_ptr;
    std::unique_ptr<boolbvt> decision_procedure_is_boolbvt_ptr;
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
  void set_decision_procedure_time_limit(
    solver_resource_limitst &decision_procedure);

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
  " {y--sat-solver} {usolver} \t use specified SAT solver\n"                   \
  " {y--external-sat-solver} {ucmd} \t command to invoke SAT solver process\n" \
  " {y--no-sat-preprocessor} \t disable the SAT solver's simplifier\n"         \
  " {y--dimacs} \t generate CNF in DIMACS format\n"                            \
  " {y--beautify} \t beautify the counterexample (greedy heuristic)\n"         \
  " {y--smt1} \t use default SMT1 solver (obsolete)\n"                         \
  " {y--smt2} \t use default SMT2 solver (Z3)\n"                               \
  " {y--bitwuzla} \t use Bitwuzla\n"                                           \
  " {y--boolector} \t use Boolector\n"                                         \
  " {y--cprover-smt2} \t use CPROVER SMT2 solver\n"                            \
  " {y--cvc3} \t use CVC3\n"                                                   \
  " {y--cvc4} \t use CVC4\n"                                                   \
  " {y--cvc5} \t use CVC5\n"                                                   \
  " {y--mathsat} \t use MathSAT\n"                                             \
  " {y--yices} \t use Yices\n"                                                 \
  " {y--z3} \t use Z3\n"                                                       \
  " {y--fpa} \t use theory of floating-point arithmetic\n"                     \
  " {y--refine} \t use refinement procedure (experimental)\n"                  \
  " {y--refine-arrays} \t use refinement for arrays only\n"                    \
  " {y--refine-arithmetic} \t refinement of arithmetic expressions only\n"     \
  " {y--max-node-refinement} \t "                                              \
  "maximum refinement iterations for arithmetic expressions\n"                 \
  " {y--incremental-smt2-solver} {ucmd} \t "                                   \
  "command to invoke external SMT solver for incremental solving "             \
  "(experimental)\n"                                                           \
  " {y--outfile} {ufilename} \t output formula to given file\n"                \
  " {y--dump-smt-formula} {ufilename} \t "                                     \
  "output smt incremental formula to the given file\n"                         \
  " {y--write-solver-stats-to} {ujson-file} \t "                               \
  "collect the solver query complexity\n"

#endif // CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

/*******************************************************************\

Module: measure and track the complexity of solver queries

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SOLVER_HARDNESS_H
#define CPROVER_SOLVERS_SOLVER_HARDNESS_H

#include <solvers/hardness_collector.h>
#include <solvers/prop/prop_conv_solver.h>

#include <fstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <goto-programs/goto_program.h>

#include <util/optional.h>

/// A structure that facilitates collecting the complexity statistics from a
/// decision procedure. The idea is to associate some solver complexity metric
/// with each line-of-code, GOTO instruction, and SSA step. The motivation is to
/// be able to track the impact of (1) which C instruction to use on the code
/// level, (2) which GOTO instruction to generate when parsing the source or
/// running internal optimisations, (3) which SSA step to produce for each GOTO
/// instruction, etc.
///
/// In terms of a SAT solver the complexity metric can be number of
/// clauses/literals/variables.
///
/// The object of this type should be visible from the \ref
/// symex_target_equationt (so that we can register which SSA/GOTO/program
/// counter was passed to the solver) and from some decision procedure (e.g. a
/// derived class of \ref cnft for SAT solving). For this purpose the object
/// lives in the \ref solver_factoryt::solvert and pointers are passed to both
/// \ref decision_proceduret and \ref propt.
struct solver_hardnesst : public clause_hardness_collectort
{
  // From SAT solver we collect the number of clauses, the number of literals
  // and the number of distinct variables that were used in all clauses.
  struct sat_hardnesst
  {
    size_t clauses = 0;
    size_t literals = 0;
    std::unordered_set<size_t> variables = {};
    std::vector<size_t> clause_set = {};

    sat_hardnesst &operator+=(const sat_hardnesst &other);
  };

  // Associate an SSA step expression (the one passed to the solver: the guard
  // for GOTO; equality for ASSIGN, etc.) with the SAT hardness of the resulting
  // query. The GOTO and source level instructions are stored as \ref
  // goto_programt::const_targett.
  struct hardness_ssa_keyt
  {
    std::string ssa_expression;
    goto_programt::const_targett pc;

    bool operator==(const hardness_ssa_keyt &other) const;
  };

  // As above but for the special case of multiple assertions, which are
  // presented to the solver as a single disjunction. Hence we have one SSA
  // expression (the whole disjunction) and multiple program counters.
  struct assertion_statst
  {
    sat_hardnesst sat_hardness;
    std::string ssa_expression;
    std::vector<goto_programt::const_targett> pcs;

    bool empty() const;
  };

  /// Called from the `symtex_target_equationt::convert_*`, this function
  ///   associates an SSA step to all the solver queries collected since the
  ///   last call.
  /// \param ssa_index: position (of this step) in the SSA equation
  /// \param ssa_expression: string representing the SSA step expression
  /// \param pc: the GOTO instruction iterator for this SSA step
  void register_ssa(
    std::size_t ssa_index,
    const exprt ssa_expression,
    goto_programt::const_targett pc);

  void register_ssa_size(std::size_t size);

  /// Called from the `symtex_target_equationt::convert_assertions`, this
  ///   function associates the disjunction of assertions to all the solver
  ///   queries collected since the last call.
  /// \param ssa_expression: string representing the disjuction of SSA
  ///   assertions
  /// \param pcs: all GOTO instruction iterators that contributed in the
  ///   disjunction
  void register_assertion_ssas(
    const exprt ssa_expression,
    const std::vector<goto_programt::const_targett> &pcs);

  /// Called e.g. from the `satcheck_minisat2::lcnf`, this function adds the
  ///   complexity statistics from the last SAT query to the `current_ssa_key`.
  /// \param bv: the clause (vector of literals)
  /// \param cnf: processed clause
  /// \param cnf_clause_index: index of clause in dimacs output
  /// \param register_cnf: negation of boolean variable tracking if the clause
  /// can be eliminated
  void register_clause(
    const bvt &bv,
    const bvt &cnf,
    const size_t cnf_clause_index,
    bool register_cnf);

  void set_outfile(const std::string &file_name);

  /// Print the statistics to a JSON file (specified via command-line option).
  void produce_report();

  solver_hardnesst() = default;

  // copying this isn’t really a meaningful operation
  solver_hardnesst(const solver_hardnesst &) = delete;
  solver_hardnesst(solver_hardnesst &&) = default;

  // copying this isn’t really a meaningful operation
  solver_hardnesst &operator=(const solver_hardnesst &) = delete;
  solver_hardnesst &operator=(solver_hardnesst &&) = default;

  const std::vector<std::unordered_map<hardness_ssa_keyt, sat_hardnesst>> get_hardness_stats() const;


private:
  // A minor modification of \ref goto_programt::output_instruction
  static std::string goto_instruction2string(goto_programt::const_targett pc);

  static std::string expr2string(const exprt expr);

  std::string outfile;
  std::vector<std::unordered_map<hardness_ssa_keyt, sat_hardnesst>>
    hardness_stats;
  hardness_ssa_keyt current_ssa_key;
  sat_hardnesst current_hardness;
  assertion_statst assertion_stats;
  std::size_t max_ssa_set_size;
};

// NOLINTNEXTLINE(readability/namespace)
namespace std
{
template <>
// NOLINTNEXTLINE(readability/identifiers)
struct hash<solver_hardnesst::hardness_ssa_keyt>
{
  std::size_t
  operator()(const solver_hardnesst::hardness_ssa_keyt &hashed_stats) const
  {
    return std::hash<std::string>{}(
      hashed_stats.ssa_expression +
      hashed_stats.pc->source_location().as_string());
  }
};
} // namespace std

static inline void with_solver_hardness(
  decision_proceduret &maybe_hardness_collector,
  std::function<void(solver_hardnesst &hardness)> handler)
{
  // FIXME I am wondering if there is a way to do this that is a bit less
  // dynamically typed.
  if(
    auto prop_conv_solver =
      dynamic_cast<prop_conv_solvert *>(&maybe_hardness_collector))
  {
    if(auto hardness_collector = prop_conv_solver->get_hardness_collector())
    {
      if(hardness_collector->solver_hardness)
      {
        auto &solver_hardness = static_cast<solver_hardnesst &>(
          *(hardness_collector->solver_hardness));
        handler(solver_hardness);
      }
    }
  }
}

#endif // CPROVER_SOLVERS_SOLVER_HARDNESS_H

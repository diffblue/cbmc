/*******************************************************************\

Module: Word-level Proof Explanation

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Word-level Proof Explanation

#ifndef CPROVER_GOTO_CHECKER_PROOF_EXPLANATION_H
#define CPROVER_GOTO_CHECKER_PROOF_EXPLANATION_H

#include <util/irep.h>
#include <util/source_location.h>

#include <string>
#include <type_traits>
#include <vector>

class namespacet;
class stack_decision_proceduret;
class symex_target_equationt;

/// A single step in a proof explanation, representing a program step
/// that contributes to proving a property.
struct proof_explanation_stept
{
  /// Source location of the contributing step
  source_locationt source_location;

  /// Type of the contributing step (e.g., "assignment", "assumption")
  std::string step_type;

  /// Human-readable description of why this step contributes
  std::string description;

  /// Whether this step is in the unsat core (true by default
  /// for backward compatibility with the basic approach)
  bool in_core = true;
};

/// Extract a word-level proof explanation from an UNSAT result.
/// After the solver returns UNSATISFIABLE, this function iterates
/// over the SSA steps in the equation and identifies which steps
/// contribute to the proof. Steps that are not sliced away and
/// have non-trivial guards or conditions are collected.
/// \param equation: the SSA equation after solving
/// \param ns: the namespace for expression pretty-printing
/// \return a vector of proof explanation steps
std::vector<proof_explanation_stept> get_proof_explanation(
  const symex_target_equationt &equation,
  const namespacet &ns);

/// Extract a word-level proof explanation with unsat core information.
/// After the solver returns UNSATISFIABLE, this function iterates
/// over the SSA steps in the equation and identifies which steps
/// contribute to the proof. Additionally, it uses the solver's
/// assumption-based conflict analysis to determine which steps are
/// truly in the unsat core. Steps whose guard handles are in the
/// conflict are marked with in_core=true.
/// \param equation: the SSA equation after solving
/// \param solver: the decision procedure (must support push/pop)
/// \param ns: the namespace for expression pretty-printing
/// \return a vector of proof explanation steps with core annotations
std::vector<proof_explanation_stept> get_proof_explanation_with_core(
  const symex_target_equationt &equation,
  stack_decision_proceduret &solver,
  const namespacet &ns);

/// A word-level invariant extracted from the proof explanation.
/// Groups related constraints by the variable they constrain.
struct proof_invariantt
{
  /// The variable this invariant is about (original SSA name)
  irep_idt variable;

  /// Source-level name of the variable (without SSA suffixes)
  std::string display_name;

  /// The human-readable expressions constraining this variable
  std::vector<std::string> constraints;
};

/// Extract word-level invariants from a proof explanation.
/// Groups core steps by the variables they constrain and
/// produces one invariant summary per variable.
/// \param explanation: the proof explanation steps (with core info)
/// \param equation: the SSA equation used during analysis
/// \param ns: the namespace for expression pretty-printing
/// \return a vector of proof invariants, one per variable
std::vector<proof_invariantt> extract_proof_invariants(
  const std::vector<proof_explanation_stept> &explanation,
  const symex_target_equationt &equation,
  const namespacet &ns);

/// Type trait to detect whether a checker type T
/// has a get_proof_explanation() method.
template <typename T, typename = void>
struct has_get_proof_explanationt : std::false_type
{
};

template <typename T>
struct has_get_proof_explanationt<
  T,
  std::void_t<decltype(std::declval<T>().get_proof_explanation())>>
  : std::true_type
{
};

/// Type trait to detect whether a checker type T
/// has a get_proof_invariants() method.
template <typename T, typename = void>
struct has_get_proof_invariantst : std::false_type
{
};

template <typename T>
struct has_get_proof_invariantst<
  T,
  std::void_t<decltype(std::declval<T>().get_proof_invariants())>>
  : std::true_type
{
};

#endif // CPROVER_GOTO_CHECKER_PROOF_EXPLANATION_H

/*******************************************************************\

Module: String support via creating string constraints and progressively
        instantiating the universal constraints as needed.
        The procedure is described in the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

/// \file
/// String support via creating string constraints and progressively
///   instantiating the universal constraints as needed. The procedure is
///   described in the PASS paper at HVC'13: "PASS: String Solving with
///   Parameterized Array and Interval Automaton" by Guodong Li and Indradeep
///   Ghosh

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H

#include <limits>
#include <util/string_expr.h>
#include <util/replace_expr.h>
#include <util/union_find_replace.h>

#include "string_constraint.h"
#include "string_constraint_generator.h"
#include "string_refinement_invariant.h"
#include "string_refinement_util.h"

// clang-format off
#define OPT_STRING_REFINEMENT \
  "(no-refine-strings)" \
  "(string-printable)" \
  "(string-input-value):" \
  "(string-non-empty)" \
  "(max-nondet-string-length):"

#define HELP_STRING_REFINEMENT \
  " --no-refine-strings          turn off string refinement\n" \
  " --string-printable           restrict to printable strings (experimental)\n" /* NOLINT(*) */ \
  " --string-non-empty           restrict to non-empty strings (experimental)\n" /* NOLINT(*) */ \
  " --string-input-value st      restrict non-null strings to a fixed value st;\n" /* NOLINT(*) */ \
  "                              the switch can be used multiple times to give\n" /* NOLINT(*) */ \
  "                              several strings\n" /* NOLINT(*) */ \
  " --max-nondet-string-length n bound the length of nondet (e.g. input) strings\n" /* NOLINT(*) */

// The integration of the string solver into CBMC is incomplete. Therefore,
// it is not turned on by default and not all options are available.
#define OPT_STRING_REFINEMENT_CBMC \
  "(refine-strings)" \
  "(string-printable)"

#define HELP_STRING_REFINEMENT_CBMC \
  " --refine-strings             use string refinement (experimental)\n" \
  " --string-printable           restrict to printable strings (experimental)\n" /* NOLINT(*) */
// clang-format on

#define DEFAULT_MAX_NB_REFINEMENT std::numeric_limits<size_t>::max()

class string_refinementt final: public bv_refinementt
{
private:
  struct configt
  {
    std::size_t refinement_bound=0;
    bool use_counter_example=true;
  };
public:
  /// string_refinementt constructor arguments
  struct infot : public bv_refinementt::infot,
                 public configt
  {
  };

  explicit string_refinementt(const infot &);

  std::string decision_procedure_text() const override
  { return "string refinement loop with "+prop.solver_text(); }

  exprt get(const exprt &expr) const override;
  void set_to(const exprt &expr, bool value) override;
  decision_proceduret::resultt dec_solve() override;

private:
  // Base class
  typedef bv_refinementt supert;

  string_refinementt(const infot &, bool);

  const configt config_;
  std::size_t loop_bound_;
  string_constraint_generatort generator;

  // Simple constraints that have been given to the solver
  std::set<exprt> seen_instances;

  string_axiomst axioms;

  // Unquantified lemmas that have newly been added
  std::vector<exprt> current_constraints;

  // See the definition in the PASS article
  // Warning: this is indexed by array_expressions and not string expressions

  index_set_pairt index_sets;
  union_find_replacet symbol_resolve;

  std::vector<equal_exprt> equations;

  string_dependenciest dependencies;

  void add_lemma(const exprt &lemma, bool simplify_lemma = true);
};

exprt substitute_array_lists(exprt expr, std::size_t string_max_length);

// Declaration required for unit-test:
union_find_replacet string_identifiers_resolution_from_equations(
  std::vector<equal_exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream);

// Declaration required for unit-test:
exprt substitute_array_access(
  exprt expr,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator,
  const bool left_propagate);

#endif

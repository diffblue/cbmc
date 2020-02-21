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
#include <util/magic.h>
#include <util/replace_expr.h>
#include <util/string_expr.h>
#include <util/union_find_replace.h>

#include "max_concrete_char_array.h"
#include "string_constraint.h"
#include "string_constraint_generator.h"
#include "string_dependencies.h"
#include "string_refinement_invariant.h"
#include "string_refinement_util.h"

// clang-format off
#define OPT_STRING_REFINEMENT \
  "(no-refine-strings)" \
  "(string-printable)" \
  "(string-input-value):" \
  "(string-non-empty)" \
  "(max-nondet-string-length):" \
  "(max-intermediate-string-length):" \
  "(store-constants-in-index-sets)"

#define HELP_STRING_REFINEMENT \
  " --no-refine-strings          turn off string refinement\n" \
  " --string-printable           restrict to printable strings and characters\n" /* NOLINT(*) */ \
  " --string-non-empty           restrict to non-empty strings (experimental)\n" /* NOLINT(*) */ \
  " --string-input-value st      restrict non-null strings to a fixed value st;\n" /* NOLINT(*) */ \
  "                              the switch can be used multiple times to give\n" /* NOLINT(*) */ \
  "                              several strings\n" /* NOLINT(*) */ \
  " --max-nondet-string-length n bound the length of nondet (e.g. input) strings.\n" /* NOLINT(*) */ \
  "                              Default is " + std::to_string(MAX_CONCRETE_STRING_SIZE - 1) + "; note that\n" /* NOLINT(*) */ \
  "                              setting the value higher than this does not work\n" /* NOLINT(*) */ \
  "                              with --trace or --validate-trace.\n" /* NOLINT(*) */ \
  " --max-intermediate-string-length n bound the length of intermediate\n"  /* NOLINT(*) */ \
  "                              strings introduced by string operations such\n"  /* NOLINT(*) */ \
  "                              as concatenation, substring operations, etc.\n"  /* NOLINT(*) */ \
  "                              If this is less than or equal to " +  /* NOLINT(*) */ \
    std::to_string(max_concrete_char_array_length) +  /* NOLINT(*) */ \
    " then such\n" /* NOLINT(*) */ \
  "                              strings will be represented by fixed-sized\n" /* NOLINT(*) */ \
  "                              arrays to the backend solver, which can\n" /* NOLINT(*) */ \
  "                              affect solver performance.\n" /* NOLINT(*) */ \
  " --store-constants-in-index-sets store constant indices observed in a\n" /* NOLINT(*) */ \
  "                              previous model in strings' index sets,\n" /* NOLINT(*) */ \
  "                              rather than symbolic expressions as usual.\n" /* NOLINT(*) */ \
  "                              May reduce string solving memory usage, but\n" /* NOLINT(*) */ \
  "                              may cause it to take more iterations to\n" /* NOLINT(*) */ \
  "                              converge." /* NOLINT(*) */

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

class string_refinementt final : public bv_refinementt
{
private:
  struct configt
  {
    std::size_t refinement_bound = 0;
    bool use_counter_example = true;
    /// If set, all intermediate strings created by the solver (e.g. the
    /// result of substring, concatenation and so on) are bounded by the
    /// given maximum length. This can mean strings are represented by
    /// constant-sized arrays, which can be much cheaper to solve against.
    optionalt<std::size_t> maximum_intermediate_string_length;
    /// If set, the string solver's index sets are maintained in terms of
    /// constant rather than symbolic expressions. For example, normally we
    /// might note that 'a' is used in the contexts 'a[x]', 'a[y]' and 'a[z]',
    /// and so instantiate universal constraints involving 'a' for each symbol
    /// or expression 'x', 'y' and 'z'. With this option set, we instead
    /// evaluate each expression against a tentative model and instantiate for
    /// each concrete offset (so if 'x' = '2', 'y' = 4' and 'z' = '2' in a
    /// given model we'll instantiate two copies of our universal axioms, for
    /// offsets 2 and 4).
    /// Using concrete values like this can save a lot of time and memory
    /// when universal constraints simplify a lot against a constant or there
    /// are many symbolic indices referring to the same offset. On the other
    /// hand it can be more expensive if each iteration of the refinement
    /// loop picks a different valuation for the symbolic offset expressions.
    bool store_constants_in_index_set;
  };

public:
  /// string_refinementt constructor arguments
  struct infot : public bv_refinementt::infot, public configt
  {
  };

  explicit string_refinementt(const infot &);

  std::string decision_procedure_text() const override
  {
    return "string refinement loop with " + prop.solver_text();
  }

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

  std::vector<exprt> equations;

  string_dependenciest dependencies;

  void add_lemma(const exprt &lemma, bool simplify_lemma = true);

  interval_sparse_arrayt restrict_sparse_array_to_index_set(
    interval_sparse_arrayt array,
    const std::set<exprt> &index_set) const;

  std::vector<size_t>
  get_model_defined_indices(const std::set<exprt> &index_set) const;
};

exprt substitute_array_lists(exprt expr, std::size_t string_max_length);

// Declaration required for unit-test:
union_find_replacet string_identifiers_resolution_from_equations(
  const std::vector<equal_exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream);

// Declaration required for unit-test:
exprt substitute_array_access(
  exprt expr,
  symbol_generatort &symbol_generator,
  const bool left_propagate);

#endif

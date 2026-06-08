/// \file
/// Gaussian elimination propagator for CaDiCaL.
/// Tracks XOR constraints and propagates forced assignments via GF(2)
/// row reduction during CDCL search.

#ifndef CPROVER_SOLVERS_SAT_XOR_GAUSS_H
#define CPROVER_SOLVERS_SAT_XOR_GAUSS_H

#include <solvers/prop/literal.h>
#include "xor_propagator.h"

#include <cstdint>
#include <unordered_map>
#include <vector>

/// A single XOR constraint: x1 XOR x2 XOR ... XOR xn = rhs

/// Sparse GF(2) row: a set of column indices + parity bit.
/// Stored as a sorted vector for efficient XOR (merge).
struct gf2_rowt
{
  std::vector<unsigned> cols; // sorted column indices
  bool rhs = false;
  std::vector<size_t> origins; // indices into original_xors

  /// XOR this row with another (symmetric difference of columns)
  void xor_with(const gf2_rowt &other)
  {
    std::vector<unsigned> merged;
    merged.reserve(cols.size() + other.cols.size());
    auto i = cols.begin(), ie = cols.end();
    auto j = other.cols.begin(), je = other.cols.end();
    while(i != ie && j != je)
    {
      if(*i < *j)
        merged.push_back(*i++);
      else if(*i > *j)
        merged.push_back(*j++);
      else
      {
        ++i;
        ++j;
      } // cancel
    }
    merged.insert(merged.end(), i, ie);
    merged.insert(merged.end(), j, je);
    cols = std::move(merged);
    rhs ^= other.rhs;
    // Merge origins
    origins.insert(origins.end(), other.origins.begin(), other.origins.end());
  }

  bool is_empty() const
  {
    return cols.empty();
  }
  bool is_unit() const
  {
    return cols.size() == 1;
  }
  bool is_conflict() const
  {
    return cols.empty() && rhs;
  }
};

/// Gaussian elimination over GF(2) with incremental updates.
/// Maintains a matrix in row echelon form. When a variable is assigned,
/// substitutes it and checks for unit propagations or conflicts.
class xor_gausst
{
public:
  /// Add a XOR constraint to the system
  void add_xor(const xor_constraintt &xor_clause);

  /// Notify that a variable has been assigned
  void assign(unsigned var, bool value);

  /// Undo assignments back to a given trail size
  void backtrack(size_t trail_size);

  /// Get the next propagation, or 0 if none
  int propagate();

  /// Get the reason clause for a propagation as DIMACS literals.
  /// Returns the XOR row as a clause: the propagated literal plus
  /// the negation of each assigned literal in the row.
  std::vector<int> get_reason(int propagated_lit);

  bool has_conflict() const;
  std::vector<int> get_conflict_clause();

  /// Matrix rank (number of linearly independent rows)
  size_t get_rank() const
  {
    return rank;
  }

  /// Number of XOR constraints
  size_t num_xors() const
  {
    return matrix.size();
  }

  /// Suggest the best decision variable: the unassigned variable appearing
  /// in the most matrix rows. Returns DIMACS literal (positive) or 0.
  int suggest_decision() const;

  /// Current trail size (for backtracking)
  size_t trail_size() const
  {
    return trail.size();
  }

private:
  /// The matrix rows (in partial row echelon form)
  std::vector<gf2_rowt> matrix;

  /// Original XOR constraints (for reason clause reconstruction)
  std::vector<xor_constraintt> original_xors;
  std::vector<size_t> matrix_to_original;

  /// Matrix rank
  size_t rank = 0;

  /// For each variable, which rows contain it (for fast substitution)
  std::vector<std::vector<size_t>> var_to_rows;

  /// Assignment trail: (variable, old_value) pairs for backtracking
  struct trail_entryt
  {
    unsigned var;
    // Snapshot of rows that were modified (for undo)
    std::vector<std::pair<size_t, gf2_rowt>> row_snapshots;
  };
  std::vector<trail_entryt> trail;

  /// Current variable assignments: 0=unassigned, 1=true, -1=false
  std::vector<int8_t> assignments;

  /// Queue of unit propagations found
  std::vector<int> prop_queue;

  /// Current conflict row (if any)
  int conflict_row = -1;

  /// Stored conflict clause (built eagerly at detection time)
  std::vector<int> stored_conflict;

  /// Stored reason clauses, keyed by propagated literal
  std::unordered_map<int, std::vector<int>> stored_reasons;

  /// Row that caused each propagation (for reason generation)
  std::vector<int> prop_reason_row; // indexed by variable

  void ensure_var(unsigned var);
  void substitute_and_check(unsigned var, bool value, trail_entryt &entry);
  void build_conflict_clause(int row_idx);
};

#endif // CPROVER_SOLVERS_SAT_XOR_GAUSS_H

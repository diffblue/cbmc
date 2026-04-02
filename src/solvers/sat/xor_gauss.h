/// \file
/// Gaussian elimination propagator for CaDiCaL.
/// Tracks XOR constraints and propagates forced assignments via GF(2)
/// row reduction during CDCL search.

#ifndef CPROVER_SOLVERS_SAT_XOR_GAUSS_H
#define CPROVER_SOLVERS_SAT_XOR_GAUSS_H

#include <solvers/prop/literal.h>

#include <cstdint>
#include <vector>

/// A single XOR constraint: x1 XOR x2 XOR ... XOR xn = rhs
struct xor_constraintt
{
  std::vector<unsigned> vars; // variable indices (1-based, as in DIMACS)
  bool rhs;                   // parity (true = odd number of trues)
};

/// Sparse GF(2) row: a set of column indices + parity bit.
/// Stored as a sorted vector for efficient XOR (merge).
struct gf2_rowt
{
  std::vector<unsigned> cols; // sorted column indices
  bool rhs = false;

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

  /// Number of XOR constraints
  size_t num_xors() const
  {
    return matrix.size();
  }

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

  /// Row that caused each propagation (for reason generation)
  std::vector<int> prop_reason_row; // indexed by variable

  void ensure_var(unsigned var);
  void substitute_and_check(unsigned var, bool value, trail_entryt &entry);
};

#endif // CPROVER_SOLVERS_SAT_XOR_GAUSS_H

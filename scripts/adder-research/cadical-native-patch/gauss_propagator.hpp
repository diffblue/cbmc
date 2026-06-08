// Native Gaussian elimination propagator for CaDiCaL.
// Maintains XOR constraints and propagates via GF(2) row reduction.
#ifndef _gauss_propagator_hpp_INCLUDED
#define _gauss_propagator_hpp_INCLUDED

#include <vector>
#include <cstdint>
#include <cstdlib>
#include <algorithm>
#include "cadical.hpp"

namespace CaDiCaL {

struct GaussRow {
  std::vector<unsigned> cols; // sorted column indices
  bool rhs = false;

  void xor_with(const GaussRow &other) {
    std::vector<unsigned> merged;
    merged.reserve(cols.size() + other.cols.size());
    auto i = cols.begin(), ie = cols.end();
    auto j = other.cols.begin(), je = other.cols.end();
    while (i != ie && j != je) {
      if (*i < *j) merged.push_back(*i++);
      else if (*i > *j) merged.push_back(*j++);
      else { ++i; ++j; }
    }
    merged.insert(merged.end(), i, ie);
    merged.insert(merged.end(), j, je);
    cols = std::move(merged);
    rhs ^= other.rhs;
  }

  bool is_empty() const { return cols.empty(); }
  bool is_unit() const { return cols.size() == 1; }
  bool is_conflict() const { return cols.empty() && rhs; }
};

struct GaussXOR {
  std::vector<unsigned> vars;
  bool rhs;
};

class GaussPropagator {
public:
  void add_xor(const std::vector<unsigned> &vars, bool rhs) {
    if (rank_ >= 1000) return;

    GaussXOR xc{vars, rhs};
    original_xors.push_back(xc);

    GaussRow row;
    row.rhs = rhs;
    for (unsigned v : vars) {
      ensure_var(v);
      if (assignments[v] != 0) {
        if (assignments[v] == 1) row.rhs = !row.rhs;
      } else {
        row.cols.push_back(v);
      }
    }
    std::sort(row.cols.begin(), row.cols.end());

    // Gaussian reduction
    for (size_t i = 0; i < matrix.size(); ++i) {
      if (matrix[i].is_empty()) continue;
      if (!row.is_empty() && row.cols.front() == matrix[i].cols.front())
        row.xor_with(matrix[i]);
    }

    if (row.is_conflict()) {
      conflict_row = static_cast<int>(matrix.size());
      // Build conflict clause eagerly
      stored_conflict.clear();
      for (unsigned v : xc.vars) {
        if (v < assignments.size() && assignments[v] != 0)
          stored_conflict.push_back(assignments[v] == 1 ? -(int)v : (int)v);
      }
      matrix.push_back(std::move(row));
      return;
    }

    if (row.is_unit()) {
      unsigned v = row.cols[0];
      int lit = row.rhs ? static_cast<int>(v) : -static_cast<int>(v);
      prop_queue.push_back(lit);
      prop_reason_row[v] = static_cast<int>(matrix.size());
    }

    if (!row.is_empty()) {
      size_t idx = matrix.size();
      for (unsigned c : row.cols)
        var_to_rows[c].push_back(idx);
      matrix.push_back(std::move(row));
      ++rank_;
    }
  }

  void assign(unsigned var, bool value) {
    ensure_var(var);
    if (assignments[var] != 0) return;

    trail.push_back({var, {}});
    assignments[var] = value ? 1 : -1;

    auto &entry = trail.back();
    if (var < var_to_rows.size()) {
      for (size_t row_idx : var_to_rows[var]) {
        auto &row = matrix[row_idx];
        if (row.is_empty()) continue;

        entry.snapshots.push_back({row_idx, row});

        // Substitute: XOR out the assigned variable
        if (value) row.rhs = !row.rhs;
        auto it = std::lower_bound(row.cols.begin(), row.cols.end(), var);
        if (it != row.cols.end() && *it == var)
          row.cols.erase(it);

        if (row.is_conflict()) {
          conflict_row = static_cast<int>(row_idx);
          stored_conflict.clear();
          if (row_idx < original_xors.size()) {
            for (unsigned v : original_xors[row_idx].vars) {
              if (v < assignments.size() && assignments[v] != 0)
                stored_conflict.push_back(assignments[v] == 1 ? -(int)v : (int)v);
            }
          }
        } else if (row.is_unit()) {
          unsigned v = row.cols[0];
          if (assignments[v] == 0) {
            int lit = row.rhs ? static_cast<int>(v) : -static_cast<int>(v);
            prop_queue.push_back(lit);
            prop_reason_row[v] = static_cast<int>(row_idx);
          }
        }
      }
    }
  }

  void backtrack(size_t target) {
    while (trail.size() > target) {
      auto &entry = trail.back();
      assignments[entry.var] = 0;
      for (auto it = entry.snapshots.rbegin(); it != entry.snapshots.rend(); ++it)
        matrix[it->first] = std::move(it->second);
      trail.pop_back();
    }
    prop_queue.clear();
    conflict_row = -1;
    stored_conflict.clear();
  }

  // Returns DIMACS literal or 0
  int propagate() {
    while (!prop_queue.empty()) {
      int lit = prop_queue.back();
      prop_queue.pop_back();
      unsigned var = static_cast<unsigned>(abs(lit));
      if (var < assignments.size() && assignments[var] == 0)
        return lit;
    }
    return 0;
  }

  // Get reason clause for propagated literal (DIMACS literals)
  // Uses the CURRENT matrix row (after Gaussian reduction)
  std::vector<int> get_reason(int propagated_lit) {
    unsigned var = static_cast<unsigned>(abs(propagated_lit));
    int row_idx = (var < prop_reason_row.size()) ? prop_reason_row[var] : -1;
    std::vector<int> reason;
    reason.push_back(propagated_lit);
    if (row_idx >= 0 && row_idx < (int)matrix.size()) {
      for (unsigned c : matrix[row_idx].cols) {
        if (c == var) continue;
        if (c < assignments.size() && assignments[c] != 0)
          reason.push_back(assignments[c] == 1 ? -(int)c : (int)c);
      }
    }
    return reason;
  }

  bool has_conflict() const { return conflict_row >= 0; }

  std::vector<int> get_conflict_clause() {
    if (conflict_row < 0) return {};
    conflict_row = -1;
    return std::move(stored_conflict);
  }

  size_t rank() const { return rank_; }
  size_t trail_size() const { return trail.size(); }
  bool empty() const { return matrix.empty(); }
  bool has_var(unsigned v) const {
    return v < var_to_rows.size() && !var_to_rows[v].empty();
  }

  void unassign(unsigned var) {
    if (var >= assignments.size() || assignments[var] == 0) return;
    for (auto it = trail.rbegin(); it != trail.rend(); ++it) {
      if (it->var == var) {
        assignments[var] = 0;
        for (auto sit = it->snapshots.rbegin(); sit != it->snapshots.rend(); ++sit)
          matrix[sit->first] = std::move(sit->second);
        trail.erase(std::next(it).base());
        prop_queue.clear();
        conflict_row = -1;
        stored_conflict.clear();
        return;
      }
    }
    assignments[var] = 0;
  }

private:
  std::vector<GaussRow> matrix;
  std::vector<GaussXOR> original_xors;
  std::vector<std::vector<size_t>> var_to_rows;
  std::vector<int8_t> assignments;
  std::vector<int> prop_queue;
  std::vector<int> prop_reason_row;
  int conflict_row = -1;
  std::vector<int> stored_conflict;
  size_t rank_ = 0;

  struct TrailEntry {
    unsigned var;
    std::vector<std::pair<size_t, GaussRow>> snapshots;
  };
  std::vector<TrailEntry> trail;

  void ensure_var(unsigned v) {
    if (v >= assignments.size()) {
      assignments.resize(v + 1, 0);
      prop_reason_row.resize(v + 1, -1);
      var_to_rows.resize(v + 1);
    }
  }
};

} // namespace CaDiCaL

#endif

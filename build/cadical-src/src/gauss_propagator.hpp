// Offline XOR Gaussian elimination for CaDiCaL.
// Performs GF(2) elimination at add_xor time, extracts derived
// unit/binary clauses that are added to the solver.
#ifndef _gauss_propagator_hpp_INCLUDED
#define _gauss_propagator_hpp_INCLUDED

#include <vector>
#include <cstdint>
#include <algorithm>

namespace CaDiCaL {

class GaussPropagator {
public:
  void add_xor(const std::vector<unsigned> &vars, bool rhs) {
    if (vars.empty()) return;
    for (unsigned v : vars)
      if (v + 1 > num_vars) num_vars = v + 1;
    orig_vars.push_back(vars);
    orig_rhs.push_back(rhs);
  }

  // Perform Gaussian elimination and extract derived clauses.
  // Returns pairs of (clause_lits, is_unit).
  struct DerivedClause {
    std::vector<int> lits; // DIMACS literals (external)
  };

  std::vector<DerivedClause> eliminate() {
    if (orig_vars.empty()) return {};
    size_t num_xors = orig_vars.size();
    size_t words = (num_vars + 63) / 64;

    // Build packed matrix
    std::vector<uint64_t> matrix(num_xors * words, 0);
    std::vector<bool> rhs(num_xors, false);
    for (size_t i = 0; i < num_xors; i++) {
      for (unsigned v : orig_vars[i])
        matrix[i * words + v / 64] |= (1ULL << (v % 64));
      rhs[i] = orig_rhs[i];
    }

    // Gaussian elimination to echelon form
    std::vector<int> pivot_col(num_xors, -1);
    size_t cur_row = 0;
    for (unsigned col = 0; col < num_vars && cur_row < num_xors; col++) {
      // Find pivot
      int found = -1;
      for (size_t r = cur_row; r < num_xors; r++) {
        if ((matrix[r * words + col / 64] >> (col % 64)) & 1)
          { found = (int)r; break; }
      }
      if (found < 0) continue;
      if ((size_t)found != cur_row) {
        for (size_t w = 0; w < words; w++)
          std::swap(matrix[cur_row * words + w], matrix[found * words + w]);
        { bool tmp = rhs[cur_row]; rhs[cur_row] = rhs[found]; rhs[found] = tmp; }
        std::swap(pivot_col[cur_row], pivot_col[found]);
      }
      // Eliminate
      for (size_t r = 0; r < num_xors; r++) {
        if (r == cur_row) continue;
        if ((matrix[r * words + col / 64] >> (col % 64)) & 1) {
          for (size_t w = 0; w < words; w++)
            matrix[r * words + w] ^= matrix[cur_row * words + w];
          rhs[r] = rhs[r] ^ rhs[cur_row];
        }
      }
      cur_row++;
    }

    // Extract derived clauses from reduced rows
    std::vector<DerivedClause> result;
    std::vector<size_t> ternary_rows;
    for (size_t r = 0; r < cur_row; r++) {
      // Count variables in row
      std::vector<unsigned> vars;
      for (size_t w = 0; w < words; w++) {
        uint64_t bits = matrix[r * words + w];
        while (bits) {
          unsigned v = (unsigned)(w * 64 + __builtin_ctzll(bits));
          bits &= bits - 1;
          if (v < num_vars) vars.push_back(v);
        }
      }

      if (vars.empty()) {
        if (rhs[r]) {
          // 0 = 1 → UNSAT. Add empty clause.
          result.push_back({{}});
        }
        continue;
      }

      if (vars.size() == 1) {
        // Unit: v = rhs → clause {v} or {-v}
        int lit = rhs[r] ? (int)vars[0] : -(int)vars[0];
        result.push_back({{lit}});
      } else if (vars.size() == 2) {
        // Binary: v1 XOR v2 = rhs
        // rhs=0: v1 = v2 → clauses {-v1, v2}, {v1, -v2}
        // rhs=1: v1 != v2 → clauses {v1, v2}, {-v1, -v2}
        int a = (int)vars[0], b = (int)vars[1];
        if (rhs[r]) {
          result.push_back({{a, b}});
          result.push_back({{-a, -b}});
        } else {
          result.push_back({{-a, b}});
          result.push_back({{a, -b}});
        }
      } else if (vars.size() == 3) {
        ternary_rows.push_back(r);
      }
    }
    // Save matrix for conflict-time XOR resolution
    e_num_vars = num_vars;
    e_words = words;
    e_num_rows = cur_row;
    e_matrix = matrix;
    e_rhs.assign(rhs.begin(), rhs.end());
    e_pivot.assign(num_vars, -1);
    // pivot_col[r] was set during elimination
    for (size_t r = 0; r < cur_row; r++) {
      if (pivot_col[r] >= 0)
        e_pivot[pivot_col[r]] = (int)r;
    }

    // Add ternary clauses only if count is reasonable
    if (ternary_rows.size() <= 1000) {
      for (size_t r : ternary_rows) {
        std::vector<unsigned> vars;
        for (size_t w = 0; w < words; w++) {
          uint64_t bits = matrix[r * words + w];
          while (bits) {
            unsigned v = (unsigned)(w * 64 + __builtin_ctzll(bits));
            bits &= bits - 1;
            if (v < num_vars) vars.push_back(v);
          }
        }
        if (vars.size() != 3) continue;
        int a = (int)vars[0], b = (int)vars[1], c = (int)vars[2];
        if (rhs[r]) {
          result.push_back({{a, b, c}});
          result.push_back({{a, -b, -c}});
          result.push_back({{-a, b, -c}});
          result.push_back({{-a, -b, c}});
        } else {
          result.push_back({{-a, b, c}});
          result.push_back({{-a, -b, -c}});
          result.push_back({{a, -b, c}});
          result.push_back({{a, b, -c}});
        }
      }
    }
    return result;
  }

  // --- Conflict-time XOR resolution ---
  // After eliminate(), these hold the echelon form matrix.
  unsigned e_num_vars = 0;
  size_t e_words = 0;
  size_t e_num_rows = 0;
  std::vector<uint64_t> e_matrix;
  std::vector<bool> e_rhs;
  std::vector<int> e_pivot; // e_pivot[var] = row index, or -1

  // Check if variable has a pivot row in the echelon form
  bool has_pivot(unsigned var) const {
    return var < e_pivot.size() && e_pivot[var] >= 0;
  }

  // Get the pivot row index for a variable
  int get_pivot_row(unsigned var) const {
    if (var >= e_pivot.size()) return -1;
    return e_pivot[var];
  }

  // XOR row `ridx` into resolvent `res` (packed bit vector + rhs)
  void xor_into_resolvent(int ridx, std::vector<uint64_t> &res,
                          bool &res_rhs) const {
    if (ridx < 0 || ridx >= (int)e_num_rows) return;
    size_t base = ridx * e_words;
    for (size_t w = 0; w < e_words; w++)
      res[w] ^= e_matrix[base + w];
    res_rhs = res_rhs ^ e_rhs[ridx];
  }

  // Create a new resolvent (all zeros)
  std::vector<uint64_t> new_resolvent() const {
    return std::vector<uint64_t>(e_words, 0);
  }

  // Check if variable is set in resolvent
  bool resolvent_has(const std::vector<uint64_t> &res, unsigned var) const {
    if (var >= e_num_vars) return false;
    return (res[var / 64] >> (var % 64)) & 1;
  }

  // Get all variables in resolvent
  std::vector<unsigned> resolvent_vars(int ridx) const {
    if (ridx < 0 || ridx >= (int)e_num_rows) return {};
    std::vector<unsigned> vars;
    size_t base = ridx * e_words;
    for (size_t w = 0; w < e_words; w++) {
      uint64_t bits = e_matrix[base + w];
      while (bits) {
        unsigned v = (unsigned)(w * 64 + __builtin_ctzll(bits));
        bits &= bits - 1;
        if (v < e_num_vars) vars.push_back(v);
      }
    }
    return vars;
  }

  std::vector<unsigned> resolvent_vars(const std::vector<uint64_t> &res) const {
    std::vector<unsigned> vars;
    for (size_t w = 0; w < e_words; w++) {
      uint64_t bits = res[w];
      while (bits) {
        unsigned v = (unsigned)(w * 64 + __builtin_ctzll(bits));
        bits &= bits - 1;
        if (v < e_num_vars) vars.push_back(v);
      }
    }
    return vars;
  }

  // Dummy methods for compatibility with propagate.cpp hooks
  bool has_var(unsigned) const { return false; }
  void assign(unsigned, bool) {}
  void unassign(unsigned) {}
  int propagate() { return 0; }
  void clear_queue() {}
  bool empty() const { return orig_vars.empty(); }
  std::vector<int> get_stored_reason(int lit) { return {lit}; }
  std::vector<unsigned> ivar_to_evar;
  int prop_count = 0;
  bool initialized = false;

private:
  unsigned num_vars = 0;
  std::vector<std::vector<unsigned>> orig_vars;
  std::vector<bool> orig_rhs;
};

} // namespace CaDiCaL
#endif

// --- Conflict-time XOR resolution support ---
// After eliminate(), the matrix is in echelon form.
// During conflict analysis, XOR rows can be combined to produce
// shorter learned clauses.

// Kept after eliminate() for conflict-time use:
// - elim_matrix, elim_rhs, elim_pivot_row, elim_words, elim_num_vars
// Call init_conflict_matrix() after eliminate() to set these up.


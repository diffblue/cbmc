#ifndef CPROVER_SOLVERS_SAT_XOR_PROPAGATOR_H
#define CPROVER_SOLVERS_SAT_XOR_PROPAGATOR_H

#include <solvers/prop/literal.h>
#include <vector>
#include <algorithm>

struct xor_constraintt
{
  std::vector<unsigned> vars;
  bool rhs = false;
};

/// XOR constraint checker with Gaussian elimination and O(1) propagation.
class xor_checkert
{
public:
  void add_xor(const xor_constraintt &xc)
  {
    // Store original for reason clause construction
    size_t orig_idx = originals.size();
    originals.push_back(xc);

    // Build row with origin tracking
    row_t row;
    row.cols = xc.vars;
    row.rhs = xc.rhs;
    row.origins.push_back(orig_idx);
    std::sort(row.cols.begin(), row.cols.end());

    // Full Gaussian elimination: reduce to echelon form
    for(size_t i = 0; i < rows.size(); ++i)
    {
      if(rows[i].cols.empty() || row.cols.empty())
        continue;
      if(row.cols[0] == rows[i].cols[0])
        xor_rows(row, rows[i]);
    }

    if(row.cols.empty())
      return; // linearly dependent

    // Initialize tracking
    row.unassigned = static_cast<int>(row.cols.size());
    row.running_rhs = row.rhs;

    // Register the row
    size_t ri = rows.size();
    for(unsigned v : row.cols)
    {
      if(v >= var_to_rows.size())
        var_to_rows.resize(v + 1);
      var_to_rows[v].push_back(ri);
    }
    rows.push_back(std::move(row));
  }

  void assign(unsigned var, bool value)
  {
    if(var >= assignments.size())
      assignments.resize(var + 1, 0);
    if(assignments[var] != 0)
      return;
    assignments[var] = value ? 1 : -1;

    if(var >= var_to_rows.size())
      return;
    for(size_t ri : var_to_rows[var])
    {
      auto &row = rows[ri];
      if(row.cols.empty())
        continue;
      --row.unassigned;
      if(value)
        row.running_rhs = !row.running_rhs;

      if(row.unassigned == 1)
      {
        for(unsigned v : row.cols)
        {
          if(v >= assignments.size() || assignments[v] == 0)
          {
            int lit = row.running_rhs ? static_cast<int>(v)
                                      : -static_cast<int>(v);
            prop_queue.push_back({lit, static_cast<int>(ri)});
            break;
          }
        }
      }
    }
  }

  void unassign(unsigned var)
  {
    if(var >= assignments.size() || assignments[var] == 0)
      return;
    bool was_true = (assignments[var] == 1);
    assignments[var] = 0;

    if(var >= var_to_rows.size())
      return;
    for(size_t ri : var_to_rows[var])
    {
      auto &row = rows[ri];
      ++row.unassigned;
      if(was_true)
        row.running_rhs = !row.running_rhs;
    }
  }

  int find_propagation()
  {
    while(!prop_queue.empty())
    {
      auto [lit, ridx] = prop_queue.back();
      prop_queue.pop_back();
      unsigned var = static_cast<unsigned>(std::abs(lit));
      if(var < assignments.size() && assignments[var] != 0)
        continue;
      last_prop_row = ridx;
      return lit;
    }
    return 0;
  }

  /// Build reason clause from ALL original XORs that contributed to
  /// the propagating row. This is sound because the derived row is
  /// a linear combination of these originals.
  std::vector<int> get_reason(int propagated_lit) const
  {
    std::vector<int> reason;
    reason.push_back(propagated_lit);
    unsigned pvar = static_cast<unsigned>(std::abs(propagated_lit));
    if(last_prop_row >= 0 && last_prop_row < static_cast<int>(rows.size()))
    {
      for(size_t oidx : rows[last_prop_row].origins)
      {
        if(oidx >= originals.size())
          continue;
        for(unsigned v : originals[oidx].vars)
        {
          if(v == pvar)
            continue;
          if(v < assignments.size() && assignments[v] != 0)
            reason.push_back(
              assignments[v] == 1 ? -static_cast<int>(v)
                                  : static_cast<int>(v));
        }
      }
    }
    // Deduplicate
    std::sort(reason.begin() + 1, reason.end());
    reason.erase(
      std::unique(reason.begin() + 1, reason.end()), reason.end());
    return reason;
  }

  void clear_queue()
  {
    prop_queue.clear();
    last_prop_row = -1;
  }

  size_t num_xors() const { return rows.size(); }

private:
  struct row_t
  {
    std::vector<unsigned> cols; // sorted
    bool rhs = false;
    bool running_rhs = false;
    int unassigned = 0;
    std::vector<size_t> origins; // indices into originals
  };

  static void xor_rows(row_t &a, const row_t &b)
  {
    std::vector<unsigned> merged;
    auto i = a.cols.begin(), ie = a.cols.end();
    auto j = b.cols.begin(), je = b.cols.end();
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
      }
    }
    merged.insert(merged.end(), i, ie);
    merged.insert(merged.end(), j, je);
    a.cols = std::move(merged);
    a.rhs ^= b.rhs;
    a.running_rhs = a.rhs; // reset running_rhs for new row
    a.origins.insert(a.origins.end(), b.origins.begin(), b.origins.end());
  }

  std::vector<xor_constraintt> originals;
  std::vector<row_t> rows;
  std::vector<std::vector<size_t>> var_to_rows;
  std::vector<int8_t> assignments;
  std::vector<std::pair<int, int>> prop_queue;
  int last_prop_row = -1;
};

#endif

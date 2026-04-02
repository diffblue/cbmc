/// \file
/// Gaussian elimination propagator for CaDiCaL — implementation.

#include "xor_gauss.h"

#include <algorithm>

void xor_gausst::ensure_var(unsigned var)
{
  if(var >= assignments.size())
  {
    assignments.resize(var + 1, 0);
    prop_reason_row.resize(var + 1, -1);
    var_to_rows.resize(var + 1);
  }
}

void xor_gausst::add_xor(const xor_constraintt &xc)
{
  original_xors.push_back(xc);
  gf2_rowt row;
  row.rhs = xc.rhs;

  for(unsigned v : xc.vars)
  {
    ensure_var(v);
    if(assignments[v] != 0)
    {
      // Variable already assigned — substitute immediately
      if(assignments[v] == 1)
        row.rhs = !row.rhs;
      // Don't add to cols (it's eliminated)
    }
    else
    {
      row.cols.push_back(v);
    }
  }
  std::sort(row.cols.begin(), row.cols.end());
  row.origins.push_back(original_xors.size() - 1);

  if(row.is_conflict())
  {
    conflict_row = static_cast<int>(original_xors.size() - 1);
    build_conflict_clause(conflict_row);
    matrix.push_back(std::move(row));
    matrix_to_original.push_back(original_xors.size() - 1);
    return;
  }

  if(row.is_unit())
  {
    unsigned v = row.cols[0];
    int lit = row.rhs ? static_cast<int>(v) : -static_cast<int>(v);
    prop_queue.push_back(lit);
    prop_reason_row[v] = static_cast<int>(matrix.size());
  }

  if(!row.is_empty())
  {
    size_t row_idx = matrix.size();
    for(unsigned c : row.cols)
      var_to_rows[c].push_back(row_idx);
    matrix.push_back(std::move(row));
    matrix_to_original.push_back(original_xors.size() - 1);
    ++rank;
  }
}

void xor_gausst::assign(unsigned var, bool value)
{
  ensure_var(var);
  if(assignments[var] != 0)
    return; // already assigned

  trail_entryt entry;
  entry.var = var;

  substitute_and_check(var, value, entry);
  assignments[var] = value ? 1 : -1;
  trail.push_back(std::move(entry));
}

void xor_gausst::substitute_and_check(
  unsigned var,
  bool value,
  trail_entryt &entry)
{
  // For each row containing this variable, substitute and check
  auto &rows = var_to_rows[var];
  for(size_t row_idx : rows)
  {
    gf2_rowt &row = matrix[row_idx];
    if(row.is_empty())
      continue;

    // Save snapshot for backtracking
    entry.row_snapshots.emplace_back(row_idx, row);

    // Remove var from the row
    auto it = std::lower_bound(row.cols.begin(), row.cols.end(), var);
    if(it != row.cols.end() && *it == var)
    {
      row.cols.erase(it);
      if(value)
        row.rhs = !row.rhs;
    }

    if(row.is_conflict())
    {
      conflict_row = static_cast<int>(row_idx);
      build_conflict_clause(conflict_row);
    }
    else if(row.is_unit())
    {
      unsigned v = row.cols[0];
      if(assignments[v] == 0)
      {
        int lit = row.rhs ? static_cast<int>(v) : -static_cast<int>(v);
        prop_queue.push_back(lit);
        prop_reason_row[v] = static_cast<int>(row_idx);
      }
    }
  }
}

void xor_gausst::backtrack(size_t target_trail_size)
{
  while(trail.size() > target_trail_size)
  {
    trail_entryt &entry = trail.back();

    // Undo assignment
    assignments[entry.var] = 0;

    // Restore row snapshots in reverse order
    for(auto it = entry.row_snapshots.rbegin();
        it != entry.row_snapshots.rend();
        ++it)
    {
      matrix[it->first] = std::move(it->second);
    }

    trail.pop_back();
  }

  // Clear stale propagations and conflicts
  prop_queue.clear();
  conflict_row = -1;
  stored_conflict.clear();
}

int xor_gausst::propagate()
{
  while(!prop_queue.empty())
  {
    int lit = prop_queue.back();
    prop_queue.pop_back();
    unsigned var = static_cast<unsigned>(std::abs(lit));
    if(assignments[var] == 0)
      return lit;
  }
  return 0;
}

std::vector<int> xor_gausst::get_reason(int propagated_lit)
{
  unsigned var = static_cast<unsigned>(std::abs(propagated_lit));
  int row_idx = (var < prop_reason_row.size()) ? prop_reason_row[var] : -1;

  std::vector<int> reason;
  reason.push_back(propagated_lit);

  // Build reason from ALL original XORs that contributed to this row.
  // The derived row is a linear combination of these originals.
  if(row_idx >= 0 && row_idx < static_cast<int>(matrix.size()))
  {
    const auto &row = matrix[row_idx];
    for(size_t oidx : row.origins)
    {
      if(oidx < original_xors.size())
      {
        for(unsigned v : original_xors[oidx].vars)
        {
          if(v == var)
            continue;
          if(v < assignments.size() && assignments[v] != 0)
          {
            reason.push_back(
              assignments[v] == 1 ? -static_cast<int>(v)
                                  : static_cast<int>(v));
          }
        }
      }
    }
  }

  return reason;
}

bool xor_gausst::has_conflict() const
{
  return conflict_row >= 0;
}

std::vector<int> xor_gausst::get_conflict_clause()
{
  if(conflict_row < 0)
    return {};

  std::vector<int> clause;
  if(conflict_row >= 0 && conflict_row < static_cast<int>(matrix.size()))
  {
    for(size_t oidx : matrix[conflict_row].origins)
    {
      if(oidx < original_xors.size())
      {
        for(unsigned v : original_xors[oidx].vars)
        {
          if(v < assignments.size() && assignments[v] != 0)
          {
            clause.push_back(
              assignments[v] == 1 ? -static_cast<int>(v)
                                  : static_cast<int>(v));
          }
        }
      }
    }
  }
  conflict_row = -1;
  return clause;
}

int xor_gausst::suggest_decision() const
{
  // Find the unassigned variable appearing in the most matrix rows.
  unsigned best_var = 0;
  size_t best_count = 0;

  for(unsigned v = 1; v < var_to_rows.size(); ++v)
  {
    if(v < assignments.size() && assignments[v] != 0)
      continue; // already assigned
    size_t count = var_to_rows[v].size();
    if(count > best_count)
    {
      best_count = count;
      best_var = v;
    }
  }

  return best_count > 1 ? static_cast<int>(best_var) : 0;
}

void xor_gausst::build_conflict_clause(int row_idx)
{
  stored_conflict.clear();
  if(row_idx >= 0 && row_idx < static_cast<int>(matrix.size()))
  {
    for(size_t oidx : matrix[row_idx].origins)
    {
      if(oidx < original_xors.size())
      {
        for(unsigned v : original_xors[oidx].vars)
        {
          if(v < assignments.size() && assignments[v] != 0)
          {
            stored_conflict.push_back(
              assignments[v] == 1 ? -static_cast<int>(v)
                                  : static_cast<int>(v));
          }
        }
      }
    }
  }
}

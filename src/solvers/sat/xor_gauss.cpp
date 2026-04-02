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

  // Reduce against existing rows (maintain echelon form)
  for(size_t i = 0; i < matrix.size(); ++i)
  {
    if(matrix[i].is_empty())
      continue;
    if(!row.is_empty() && row.cols.front() == matrix[i].cols.front())
      row.xor_with(matrix[i]);
  }

  if(row.is_conflict())
  {
    conflict_row = static_cast<int>(matrix.size());
    matrix.push_back(std::move(row));
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

    // Reduce against existing rows to maintain echelon form
    if(!row.is_empty())
    {
      unsigned pivot = row.cols.front();
      for(size_t j = 0; j < matrix.size(); ++j)
      {
        if(j == row_idx || matrix[j].is_empty())
          continue;
        if(matrix[j].cols.front() == pivot && j < row_idx)
        {
          // Row j has the same pivot — XOR to eliminate
          entry.row_snapshots.emplace_back(row_idx, row);
          row.xor_with(matrix[j]);
          break;
        }
      }
    }

    if(row.is_conflict())
    {
      conflict_row = static_cast<int>(row_idx);
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
  int row_idx = prop_reason_row[var];

  // Build reason clause from the original XOR that produced this row.
  // The reason is: propagated_lit OR ~(assigned literals in the XOR).
  // This is sound because the XOR constraint forces the propagated value
  // when all other variables are assigned.
  std::vector<int> reason;
  reason.push_back(propagated_lit);

  if(row_idx >= 0 && row_idx < static_cast<int>(original_xors.size()))
  {
    const auto &xc = original_xors[row_idx];
    for(unsigned v : xc.vars)
    {
      if(v == var)
        continue;
      if(v < assignments.size() && assignments[v] != 0)
      {
        // Add negation of the assigned literal
        reason.push_back(assignments[v] == 1 ? -static_cast<int>(v)
                                             : static_cast<int>(v));
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

  // Build conflict clause from the original XOR.
  // All variables are assigned but the parity is wrong.
  // The conflict clause is the negation of all current assignments
  // for variables in this XOR.
  std::vector<int> clause;
  if(conflict_row < static_cast<int>(original_xors.size()))
  {
    const auto &xc = original_xors[conflict_row];
    for(unsigned v : xc.vars)
    {
      if(v < assignments.size() && assignments[v] != 0)
      {
        clause.push_back(assignments[v] == 1 ? -static_cast<int>(v)
                                             : static_cast<int>(v));
      }
    }
  }
  conflict_row = -1;
  return clause;
}

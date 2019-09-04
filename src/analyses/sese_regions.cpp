/*******************************************************************\

Module: Single-entry, single-exit region analysis

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Single-entry, single-exit region analysis

#include <sstream>

#include "cfg_dominators.h"
#include "natural_loops.h"
#include "sese_regions.h"

void sese_region_analysist::operator()(const goto_programt &goto_program)
{
  natural_loopst natural_loops;
  natural_loops(goto_program);

  // A single-entry, single-exit region is one whose entry and exit nodes
  // are in a dominator-postdominator relationship, and which are
  // *cycle equivalent*, which means that any cycle in the CFG that includes the
  // entry must include the exit and vice versa.

  // Because we have a natural-loop analysis but not a general cycle analysis,
  // we conservatively approximate the latter condition by checking that there
  // are no loops with multiple backedges (this implies there are effectively
  // two loops being described as one), and that there are no backedges not
  // associated with a natural loop (indicating a cycle with multiple entry
  // edges). Those conditions being met, it suffices to check that the would-be
  // region has its entry and exit nodes in the same natural loops; without them
  // we conservatively decline to identify any regions.

  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it)
  {
    for(auto predecessor : it->incoming_edges)
    {
      if(
        predecessor->location_number > it->location_number &&
        !natural_loops.is_loop_header(it))
      {
        // No loop header associated with this backedge; conservatively decline
        // to diagnose any SESE regions.
        return;
      }
    }
  }

  for(const auto &loop : natural_loops.loop_map)
  {
    std::size_t backedge_count = std::count_if(
      loop.first->incoming_edges.begin(),
      loop.first->incoming_edges.end(),
      [&](const goto_programt::const_targett &predecessor) {
        return loop.first->location_number < predecessor->location_number;
      });
    if(backedge_count > 1)
    {
      // Loop with multiple backedges; conservatively decline to diagnose any
      // SESE regions.
      return;
    }
  }

  // All checks passed, let's find some regions!
  compute_sese_regions(goto_program, natural_loops);
}

typedef std::
  unordered_map<goto_programt::const_targett, std::size_t, const_target_hash>
    innermost_loop_mapt;

/// Builds a map from instructions to the smallest (and therefore innermost)
/// loop they are a member of.
static innermost_loop_mapt
compute_innermost_loop_ids(const natural_loopst &natural_loops)
{
  innermost_loop_mapt innermost_loop_ids;
  std::vector<std::size_t> loop_size_by_id;

  std::size_t loop_id = 0;
  for(const auto &header_and_loop : natural_loops.loop_map)
  {
    const auto &loop = header_and_loop.second;
    loop_size_by_id.push_back(loop.size());

    for(const auto &instruction : loop)
    {
      auto emplace_result = innermost_loop_ids.emplace(instruction, loop_id);
      if(!emplace_result.second)
      {
        // Is the existing loop for this instruction larger than this one? If so
        // this is the inner of the two loops.
        if(loop_size_by_id.at(emplace_result.first->second) > loop.size())
          emplace_result.first->second = loop_id;
      }
    }

    ++loop_id;
  }

  return innermost_loop_ids;
}

static long get_innermost_loop(
  const innermost_loop_mapt &innermost_loops,
  const goto_programt::const_targett &target)
{
  auto findit = innermost_loops.find(target);
  if(findit == innermost_loops.end())
    return -1;
  else
    return (long)findit->second;
}

void sese_region_analysist::compute_sese_regions(
  const goto_programt &goto_program,
  const natural_loopst &natural_loops)
{
  const auto &dominators = natural_loops.get_dominator_info();
  cfg_post_dominatorst postdominators;
  postdominators(goto_program);

  auto innermost_loop_ids = compute_innermost_loop_ids(natural_loops);

  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it)
  {
    // Only look for regions starting at nontrivial CFG edges:

    auto successors = goto_program.get_successors(it);
    if(
      successors.size() == 1 &&
      (*successors.begin())->incoming_edges.size() == 1)
      continue;

    const auto &instruction_postdoms = postdominators.get_node(it).dominators;

    // Ideally we would start with the immediate postdominator and walk down,
    // but our current dominator analysis doesn't make it easy to determine an
    // immediate dominator.

    // Ideally I would use `optionalt<std::size_t>` here, but it triggers a
    // GCC-5 bug.
    std::size_t closest_exit_index = dominators.cfg.size();
    for(const auto &possible_exit : instruction_postdoms)
    {
      const auto possible_exit_index = dominators.get_node_index(possible_exit);
      const auto &possible_exit_node = dominators.cfg[possible_exit_index];
      const auto possible_exit_dominators =
        possible_exit_node.dominators.size();

      if(
        it != possible_exit && dominators.dominates(it, possible_exit_node) &&
        get_innermost_loop(innermost_loop_ids, it) ==
          get_innermost_loop(innermost_loop_ids, possible_exit))
      {
        // If there are several candidate region exit nodes, prefer the one with
        // the least dominators, i.e. the closest to the region entrance.
        if(
          closest_exit_index == dominators.cfg.size() ||
          dominators.cfg[closest_exit_index].dominators.size() >
            possible_exit_dominators)
        {
          closest_exit_index = possible_exit_index;
        }
      }
    }

    if(closest_exit_index < dominators.cfg.size())
    {
      auto emplace_result =
        sese_regions.emplace(it, dominators.cfg[closest_exit_index].PC);
      INVARIANT(
        emplace_result.second, "should only visit each region entry once");
    }
  }
}

static std::string trimmed_last_line(const std::string &input)
{
  auto rhs_trim_idx = input.size() - 1;
  while(rhs_trim_idx > 0 && isspace(input[rhs_trim_idx]))
    --rhs_trim_idx;

  auto lhs_trim_idx = input.rfind('\n', rhs_trim_idx);
  if(lhs_trim_idx == std::string::npos)
    lhs_trim_idx = 0;

  while(lhs_trim_idx < input.size() && isspace(input[lhs_trim_idx]))
    ++lhs_trim_idx;

  return input.substr(lhs_trim_idx, (rhs_trim_idx - lhs_trim_idx) + 1);
}

typedef std::
  unordered_map<goto_programt::const_targett, std::size_t, const_target_hash>
    program_relative_instruction_indicest;

static std::string instruction_ordinals(
  const goto_programt::const_targett &instruction,
  const program_relative_instruction_indicest
    &program_relative_instruction_indices)
{
  return "(" +
         std::to_string(program_relative_instruction_indices.at(instruction)) +
         ", " + std::to_string(instruction->location_number) + ")";
}

static std::string brief_instruction_string(
  const goto_programt &goto_program,
  const goto_programt::const_targett &instruction,
  const namespacet &ns,
  const program_relative_instruction_indicest
    &program_relative_instruction_indices)
{
  std::ostringstream ostr;
  goto_program.output_instruction(ns, "", ostr, *instruction);
  return instruction_ordinals(
           instruction, program_relative_instruction_indices) +
         " " + trimmed_last_line(ostr.str());
}

void sese_region_analysist::output(
  std::ostream &out,
  const goto_programt &goto_program,
  const namespacet &ns) const
{
  program_relative_instruction_indicest program_relative_instruction_indices;
  std::size_t next_index = 0;
  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it, ++next_index)
  {
    program_relative_instruction_indices.emplace(it, next_index);
  }
  out << "Function contains " << sese_regions.size()
      << " single-entry, single-exit regions:\n";
  for(const auto &entry_exit : sese_regions)
  {
    out << "Region starting at "
        << brief_instruction_string(
             goto_program,
             entry_exit.first,
             ns,
             program_relative_instruction_indices)
        << " ends at "
        << brief_instruction_string(
             goto_program,
             entry_exit.second,
             ns,
             program_relative_instruction_indices)
        << "\n";
  }
}

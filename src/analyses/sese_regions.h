/*******************************************************************\

Module: Single-entry, single-exit region analysis

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Single-entry, single-exit region analysis

#ifndef CPROVER_ANALYSES_SESE_REGIONS_H
#define CPROVER_ANALYSES_SESE_REGIONS_H

#include <analyses/cfg_dominators.h>
#include <analyses/natural_loops.h>
#include <util/optional.h>

class sese_region_analysist
{
public:
  void operator()(const goto_programt &goto_program);
  optionalt<goto_programt::const_targett>
  get_region_exit(goto_programt::const_targett entry) const
  {
    auto find_result = sese_regions.find(entry);
    if(find_result == sese_regions.end())
      return {};
    else
      return find_result->second;
  }

  void output(
    std::ostream &out,
    const goto_programt &goto_program,
    const namespacet &ns) const;

private:
  std::unordered_map<
    goto_programt::const_targett,
    goto_programt::const_targett,
    const_target_hash>
    sese_regions;
  void compute_sese_regions(
    const goto_programt &goto_program,
    const natural_loopst &natural_loops);
};

#endif // CPROVER_ANALYSES_SESE_REGIONS_H

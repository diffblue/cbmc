/*******************************************************************\

Module: Non-concurrency analysis

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_ANALYSES_NON_CONCURRENT_H
#define CPROVER_ANALYSES_NON_CONCURRENT_H

#include <goto-programs/goto_functions.h>
#include <util/config.h>
#include <analyses/cfg_dominators.h>
#include <analyses/lock_set_analysis_cs.h>
#include <pointer-analysis/value_set_analysis_cs.h>

#include "ai_cs.h"

class non_concurrentt
{
public:
  typedef goto_programt::const_targett locationt;

  non_concurrentt(
    const goto_functionst &goto_functions,
    in_loopt &in_loop,
    value_set_analysis_cst &value_set_analysis,
    const must_lock_set_analysis_cst &must_lock_set_analysis,
    const namespacet &ns)
    : goto_functions(goto_functions),
      in_loop(in_loop),
      value_set_analysis(value_set_analysis),
      must_lock_set_analysis(must_lock_set_analysis),
      ns(ns)
  {}

  typedef ai_cs_baset::placet placet;

  bool non_concurrent(const ai_cs_stackt &stack1, locationt loc1,
                      const ai_cs_stackt &stack2, locationt loc2)
  {
    return non_concurrent(placet(stack1, loc1), placet(stack2, loc2));
  }

  bool non_concurrent(const placet &place1,
                      const placet &place2)
  {
    bool r=false;
    r=is_non_concurrent(place1, place2);
    r|=is_lock_protected(place1, place2);

    return r;
  }

  bool is_non_concurrent(const placet &place1,
                         const placet &place2);

  bool is_lock_protected(const placet &place1,
                         const placet &place2)
  {
    assert(must_lock_set_analysis.has(place1));
    assert(must_lock_set_analysis.has(place2));

    const must_lock_set_domain_cst &mlsd1=must_lock_set_analysis[place1];
    const must_lock_set_domain_cst &mlsd2=must_lock_set_analysis[place2];

    return mlsd1.has_nonempty_intersection(mlsd2.object_map);
  }

  typedef goto_functionst::goto_functiont goto_functiont;
  const goto_functionst &goto_functions;

  in_loopt &in_loop;

  value_set_analysis_cst &value_set_analysis;
  const must_lock_set_analysis_cst &must_lock_set_analysis;
  const namespacet &ns;

  bool joined_1(
    ai_cs_stackt::framest::const_iterator bound,
    const ai_cs_stackt &stack,
    locationt loc1,
    locationt loc2);

  typedef std::set<irep_idt> recursion_sett;
  recursion_sett recursion_set;

  bool joined_2(
    const ai_cs_stackt &stack,
    locationt loc1,
    locationt loc2,
    const ai_cs_stackt &create_stack,
    locationt create_loc,
    recursion_sett &recursion_set);

  bool on_all_paths(locationt loc1, locationt loc2, locationt loc3);

  // on all paths from the entry point to the exit point
  bool on_all_paths(locationt loc);

  // loc2 is on all paths starting and ending at loc1
  bool on_all_loops(locationt loc1, locationt loc2);

  bool all_paths(
    const ai_cs_stackt &stack1,
    locationt loc1,
    const ai_cs_stackt &stack2,
    locationt loc2);

  bool has_path(locationt loc1, locationt loc2);

  bool match(
    const ai_cs_stackt &join_stack, locationt join_loc,
    const ai_cs_stackt &create_stack, locationt create_loc) const;

  typedef std::set<locationt> location_sett;

  // gather calls to functions we explore
  void gather_function_calls(
    const goto_programt &goto_program,
    location_sett &location_set);

  void gather_joins(
    const goto_programt &goto_program,
    location_sett &location_set);
};

#endif

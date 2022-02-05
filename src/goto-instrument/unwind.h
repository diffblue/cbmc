/*******************************************************************\

Module: Loop unwinding

Author: Daniel Kroening, kroening@kroening.com
        Daniel Poetzl

\*******************************************************************/

/// \file
/// Loop unwinding

#ifndef CPROVER_GOTO_INSTRUMENT_UNWIND_H
#define CPROVER_GOTO_INSTRUMENT_UNWIND_H

#include <util/json.h>
#include <goto-programs/goto_model.h>

class unwindsett;

class goto_unwindt
{
public:
  enum class unwind_strategyt
  {
    CONTINUE,
    PARTIAL,
    ASSERT_ASSUME,
    ASSUME
  };

  // unwind loop

  void unwind(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const goto_programt::const_targett loop_head,
    const goto_programt::const_targett loop_exit,
    const unsigned k, // bound for given loop
    const unwind_strategyt unwind_strategy);

  void unwind(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const goto_programt::const_targett loop_head,
    const goto_programt::const_targett loop_exit,
    const unsigned k, // bound for given loop
    const unwind_strategyt unwind_strategy,
    std::vector<goto_programt::targett> &iteration_points);

  // unwind function

  void unwind(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const unwindsett &unwindset,
    const unwind_strategyt unwind_strategy = unwind_strategyt::PARTIAL);

  // unwind all functions
  void operator()(
    goto_functionst &,
    const unwindsett &unwindset,
    const unwind_strategyt unwind_strategy=unwind_strategyt::PARTIAL);

  void operator()(
    goto_modelt &goto_model,
    const unwindsett &unwindset,
    const unwind_strategyt unwind_strategy=unwind_strategyt::PARTIAL)
  {
    operator()(
      goto_model.goto_functions, unwindset, unwind_strategy);
  }

  // unwind log

  jsont output_log_json() const
  {
    return unwind_log.output_log_json();
  }

  // log
  // - for each copied instruction the location number of the
  //   original instruction it came from
  // - for each new instruction the location number of the loop head
  //   or backedge of the loop it is associated with
  struct unwind_logt
  {
    // call after calling goto_functions.update()!
    jsont output_log_json() const;

    // remove entries that refer to the given goto program
    void cleanup(const goto_programt &goto_program)
    {
      forall_goto_program_instructions(it, goto_program)
        location_map.erase(it);
    }

    void insert(
      const goto_programt::const_targett target,
      const unsigned location_number)
    {
      auto r=location_map.insert(std::make_pair(target, location_number));
      INVARIANT(r.second, "target already exists");
    }

    typedef std::map<goto_programt::const_targett, unsigned> location_mapt;
    location_mapt location_map;
  };

  unwind_logt unwind_log;

protected:
  int get_k(
    const irep_idt func,
    const unsigned loop_id,
    const unwindsett &unwindset) const;

  // copy goto program segment and redirect internal edges
  void copy_segment(
    const goto_programt::const_targett start,
    const goto_programt::const_targett end, // exclusive
    goto_programt &goto_program); // result
};

#endif // CPROVER_GOTO_INSTRUMENT_UNWIND_H

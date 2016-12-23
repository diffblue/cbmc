/*******************************************************************\

Module: Loop unwinding

Author: Daniel Kroening, kroening@kroening.com
        Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_UNWIND_H
#define CPROVER_GOTO_INSTRUMENT_UNWIND_H

#include <util/json.h>
#include <util/json_expr.h>
#include <goto-programs/goto_program.h>

// -1: do not unwind loop
typedef std::map<irep_idt, std::map<unsigned, int>> unwind_sett;

void parse_unwindset(const std::string &us, unwind_sett &unwind_set);

class goto_unwindt
{
public:
  typedef enum { CONTINUE, PARTIAL, ASSERT, ASSUME } unwind_strategyt;

  // unwind loop

  void unwind(
    goto_programt &goto_program,
    const goto_programt::const_targett loop_head,
    const goto_programt::const_targett loop_exit,
    const unsigned k, // bound for given loop
    const unwind_strategyt unwind_strategy);

  void unwind(
    goto_programt &goto_program,
    const goto_programt::const_targett loop_head,
    const goto_programt::const_targett loop_exit,
    const unsigned k, // bound for given loop
    const unwind_strategyt unwind_strategy,
    std::vector<goto_programt::targett> &iteration_points);

  // unwind function

  void unwind(
    goto_programt &goto_program,
    const unwind_sett &unwind_set,
    const int k=-1, // -1: no global bound
    const unwind_strategyt unwind_strategy=PARTIAL);

  // unwind all functions

  void operator()(
    goto_functionst &goto_functions,
    const unsigned k, // global bound
    const unwind_strategyt unwind_strategy=PARTIAL)
  {
    const unwind_sett unwind_set;
    operator()(goto_functions, unwind_set, k, unwind_strategy);
  }

  void operator()(
    goto_functionst &goto_functions,
    const unwind_sett &unwind_set,
    const int k=-1, // -1: no global bound
    const unwind_strategyt unwind_strategy=PARTIAL);

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
      assert(r.second); // did not exist yet
    }

    typedef std::map<goto_programt::const_targett, unsigned> location_mapt;
    location_mapt location_map;
  };

  unwind_logt unwind_log;

protected:
  int get_k(
    const irep_idt func,
    const unsigned loop_id,
    const int global_k,
    const unwind_sett &unwind_set) const;

  // copy goto program segment and redirect internal edges
  void copy_segment(
    const goto_programt::const_targett start,
    const goto_programt::const_targett end, // exclusive
    goto_programt &goto_program); // result
};

#endif // CPROVER_GOTO_INSTRUMENT_UNWIND_H

/*******************************************************************\

Module: Loop unwinding setup

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Loop unwinding

#ifndef CPROVER_GOTO_INSTRUMENT_UNWINDSET_H
#define CPROVER_GOTO_INSTRUMENT_UNWINDSET_H

#include <map>
#include <string>

#include <util/irep.h>
#include <util/optional.h>

class unwindsett
{
public:
  // We have
  // 1) a global limit
  // 2) limits particular to loops and recursion
  // 3) a limit per loop/function, all threads
  // 4) a limit for a particular thread.
  // We use the most specific of the above.

  // global limit for everything
  void parse_unwind(const std::string &unwind);

  // global limit for iteration
  void parse_unwind_loops(const std::string &unwind);

  // global limit for recursion
  void parse_unwind_recursion(const std::string &unwind);

  // limit for instances of a loop
  void parse_unwindset(const std::string &unwindset);

  // queries
  optionalt<unsigned>
  get_limit(const irep_idt &loop, unsigned thread_id, bool is_iteration) const;

  // read unwindset directives from a file
  void parse_unwindset_file(const std::string &file_name);

protected:
  optionalt<unsigned> global_iteration_limit;
  optionalt<unsigned> global_recursion_limit;

  // Limit for all instances of a loop.
  // This may have 'no value'.
  typedef std::map<irep_idt, optionalt<unsigned>> loop_mapt;
  loop_mapt loop_map;

  // separate limits per thread
  using thread_loop_mapt =
    std::map<std::pair<irep_idt, unsigned>, optionalt<unsigned>>;
  thread_loop_mapt thread_loop_map;
};

#endif // CPROVER_GOTO_INSTRUMENT_UNWINDSET_H

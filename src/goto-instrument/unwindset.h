/*******************************************************************\

Module: Loop unwinding setup

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Loop unwinding

#ifndef CPROVER_GOTO_INSTRUMENT_UNWINDSET_H
#define CPROVER_GOTO_INSTRUMENT_UNWINDSET_H

#include <list>
#include <map>
#include <string>

#include <util/deprecate.h>
#include <util/irep.h>
#include <util/optional.h>

class unwindsett
{
public:
  // We have
  // 1) a global limit
  // 2) a limit per loop, all threads
  // 3) a limit for a particular thread.
  // We use the most specific of the above.

  // global limit for all loops
  void parse_unwind(const std::string &unwind);

  // limit for instances of a loop
  DEPRECATED(SINCE(2019, 11, 15, "use parse_unwindset(list) instead"))
  void parse_unwindset(const std::string &unwindset);

  // limit for instances of a loop
  void parse_unwindset(const std::list<std::string> &unwindset);

  // queries
  optionalt<unsigned> get_limit(const irep_idt &loop, unsigned thread_id) const;

  // read unwindset directives from a file
  void parse_unwindset_file(const std::string &file_name);

protected:
  optionalt<unsigned> global_limit;

  // Limit for all instances of a loop.
  // This may have 'no value'.
  typedef std::map<irep_idt, optionalt<unsigned>> loop_mapt;
  loop_mapt loop_map;

  // separate limits per thread
  using thread_loop_mapt =
    std::map<std::pair<irep_idt, unsigned>, optionalt<unsigned>>;
  thread_loop_mapt thread_loop_map;

  void parse_unwindset_one_loop(std::string loop_limit);
};

#endif // CPROVER_GOTO_INSTRUMENT_UNWINDSET_H

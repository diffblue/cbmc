/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Weak Memory Instrumentation for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H
#define CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H

#include "wmm.h"

#include <util/irep.h>

class symbol_tablet;
class value_setst;
class goto_modelt;
class message_handlert;
class goto_programt;
class messaget;

void weak_memory(
  memory_modelt model,
  value_setst &,
  goto_modelt &,
  bool SCC,
  instrumentation_strategyt event_stategy,
  bool no_cfg_kill,
  bool no_dependencies,
  loop_strategyt duplicate_body,
  unsigned max_var,
  unsigned max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool cav11_option,
  bool hide_internals,
  message_handlert &,
  bool ignore_arrays);

void introduce_temporaries(
  value_setst &,
  symbol_tablet &,
  const irep_idt &function,
  goto_programt &,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  messaget &message);

#define OPT_WMM_MEMORY_MODEL  "(mm):"

#define OPT_WMM_INSTRUMENTATION_STRATEGIES                                     \
  "(one-event-per-cycle)"                                                      \
  "(minimum-interference)"                                                     \
  "(read-first)"                                                               \
  "(write-first)"                                                              \
  "(my-events)"

#define OPT_WMM_LIMITS                                                         \
  "(max-var):"                                                                 \
  "(max-po-trans):"

#define OPT_WMM_LOOPS                                                          \
  "(force-loop-duplication)"                                                   \
  "(no-loop-duplication)"

#define OPT_WMM_MISC                                                           \
  "(scc)"                                                                      \
  "(cfg-kill)"                                                                 \
  "(no-dependencies)"                                                          \
  "(no-po-rendering)"                                                          \
  "(render-cluster-file)"                                                      \
  "(render-cluster-function)"                                                  \
  "(cav11)"                                                                    \
  "(hide-internals)"                                                           \
  "(ignore-arrays)"

#define OPT_WMM                                                                \
  OPT_WMM_MEMORY_MODEL                                                         \
  OPT_WMM_INSTRUMENTATION_STRATEGIES                                           \
  OPT_WMM_LIMITS                                                               \
  OPT_WMM_LOOPS                                                                \
  OPT_WMM_MISC

#define HELP_WMM_FULL                                                          \
  help_entry("--mm <tso,pso,rmo,power>", "instruments a weak memory model")    \
    << help_entry(                                                             \
         "--scc", "detects critical cycles per SCC (one thread per SCC)")      \
    << help_entry(                                                             \
         "--one-event-per-cycle", "only instruments one event per cycle")      \
    << help_entry(                                                             \
         "--minimum-interference", "instruments an optimal number of events")  \
    << help_entry(                                                             \
         "--my-events",                                                        \
         "only instruments events whose ids appear in inst.evt")               \
    << help_entry(                                                             \
         "--read-first, --write-first",                                        \
         "only instrument cycles where a read or  write occurs as first "      \
         "event, respectively")                                                \
    << help_entry("--max-var N", "limit cycles to N variables read/written")   \
    << help_entry("--max-po-trans N", "limit cycles to N program-order edges") \
    << help_entry("--ignore-arrays", "instrument arrays as a single object")   \
    << help_entry(                                                             \
         "--cav11",                                                            \
         "always instrument shared variables, even when they are not part of " \
         "any cycle")                                                          \
    << help_entry(                                                             \
         "--force-loop-duplication, --no-loop-duplication",                    \
         "optional program transformation to construct cycles in program "     \
         "loops")                                                              \
    << help_entry(                                                             \
         "--cfg-kill",                                                         \
         "enables symbolic execution used to reduce spurious cycles")          \
    << help_entry("--no-dependencies", "no dependency analysis")               \
    << help_entry(                                                             \
         "--no-po-rendering", "no representation of the threads in the dot")   \
    << help_entry(                                                             \
         "--hide-internals",                                                   \
         "do not include thread-internal (Rfi) events in dot output")          \
    << help_entry("--render-cluster-file", "clusterises the dot by files")     \
    << help_entry(                                                             \
         "--render-cluster-function", "clusterises the dot by functions")

#endif // CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H
